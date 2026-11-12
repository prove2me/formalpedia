-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_claim_6_2_4
-- name    : ITPIRPreproc.MatchVec.claim_6_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:26.811447+00:00
-- url     : https://prove2.me/theorems/8719ef1e-761a-4b9f-9d2b-4c9408fa4657
-- title:
--   Claim 6.2.4 — sizes, running times and streaming hint computation of the activation-bit primitive
-- statement:
--   Let the matching vectors $u_a,v_a$ ($m=2^h$ rows, dimension $d=\dim(h)$) satisfy (7) with distinct $v_a\bmod2$ and be computable with constants $C_0,c_0$ (each pair in $C_0\,d\,h^{c_0}$ work, the table in $C_0\,m\,d\,h^{c_0}$ work and $C_0\,m\,d$ storage). Then there are constants $C,c$ depending only on $C_0,c_0$, and an implementation of the §6.2 primitive (the same programs for all $h$), such that for every $h\ge3$, with $n=m^2$:
--
--   1. keys and queries have exactly $(h+1)d$ bits, hints and answers exactly $2d$ bits (all codes injective);
--   2. uniform sampling from $\mathcal R^+$ and $\mathcal R^+_i$ and testing whether $i\in S(R,\rho)$ each take $t_{\rm basic}(n)=O(hd)$ work;
--   3. $\mathrm{time}(\mathsf{Query})=O(hd)$, $\mathrm{time}(\mathsf{Decode})=O(hd)$, $\mathrm{time}(\mathsf{Hint})=md\,\mathrm{poly}(h)$, $\mathrm{time}(\mathsf{Answer})=md\,\mathrm{poly}(h)$;
--   4. for $E=m/8$, every $L\ge E$ and arbitrary input keys $(R_j,\rho_j)\in\mathcal R^+$, $j\in[L]$, the streaming algorithm processes $D$ in $E$ consecutive chunks of $8m$ bits and returns $(\mathsf{Hint}(D,(R_j,\rho_j)))_{j\in[L]}$, with initialization time, time per chunk and total client storage at most $L\,t_{\rm stream}(n)$, where $t_{\rm stream}(n)=d\,\mathrm{poly}(h)$; storage includes the input keys, the vector tables and the workspace.
--
--   All bounds are worst-case, with $O(hd)=C\,h\,d$, $md\,\mathrm{poly}(h)=C\,m\,d\,h^c$ and $d\,\mathrm{poly}(h)=C\,d\,h^c$. In the language of §4.1, the implementation meets the efficiency requirements with these parameters.
--
--   This is the efficiency half of Lemma 6.2.
--
--   Differences from the source:
--   - reading: the construction's running times, sizes and streaming bounds → existence of word-RAM programs (and injective bit codes) implementing the defined algorithms (14)–(17) and the streaming hint computation within the stated worst-case bounds; reason: the paper describes its algorithms in prose; a running time is a property of an implementation in the RAM model of §3
--   - reading: O(hd), md poly(h), d poly(h) → C·h·d, C·m·d·h^c, C·d·h^c with C, c depending only on the constants C₀, c₀ with which the matching vectors are computable; reason: O(·) and poly(·) as constants chosen before h, the family and the programs; the matching vectors' own computation cost is the only input they can depend on
--   - generalization: the construction with the matching vectors of §5.2 (Appendix A) → the construction with every matching-vector family that satisfies (7) with distinct v_a mod 2 and is computable with constants C₀, c₀; one implementation for all h ≥ 3; reason: the §5.2 family is such a family (the matching_vectors_eq7 milestone), so the statement specializes to the paper's
--   - encoding: the client retains both vector tables; storage includes the vector tables → the vector tables are the implementation's public table, given to the client programs and charged to the streaming budget E·t_stream; reason: §6.2 and Claim 6.2.4 count the tables in the streaming initialization and storage
--   - encoding: time(A) is the worst-case bit work, including input and output processing → each time bound also bounds the length of the program's explicit arguments; outputs are charged by the machine; reason: the definition of time(·) on p.14
--   - encoding: E = m/8 consecutive chunks of 8m bits; streaming algorithm → E = ⌊m/8⌋ chunks of ⌈n/E⌉ = 8m bits, the streaming algorithm as an initialization program and a per-chunk program with a bit-string state; reason: for m = 2^h ≥ 8 the chunk length is exactly 8m; a suspended streaming computation is its state
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Claim 6.2.4, printed p.23 (PDF p.25)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_ActivationPrimitive
import Definitions.Def_ITPIRPreproc_MatchVec_Efficiency

open scoped ENNReal

namespace ITPIRPreproc.MatchVec

open WordRAM

/-- Claim 6.2.4, printed p.23 (PDF p.25). For a matching-vector family computable with constants
`C₀, c₀` (`d·poly(h)` per pair, `m·d·poly(h)` and `O(md)` space for the table), there are constants
`C, c` depending only on `C₀, c₀`, and word-RAM programs implementing the §6.2 primitive
(`m = 2^h`, `h ≥ 3`, `d = dim h`) such that: keys and queries have `(h+1)d` bits and hints and
answers `2d` bits (injective codes); the basic operations take `t_basic = O(hd)`;
`time(Query) = O(hd)`, `time(Decode) = O(hd)`, `time(Hint) = md·poly(h)`,
`time(Answer) = md·poly(h)`; and the streaming hint computation (`E = m/8` chunks of `8m` bits,
every `L ≥ E`, arbitrary input keys) has initialization time, time per chunk and total storage at
most `L·t_stream` with `t_stream = d·poly(h)`. All bounds are worst-case. -/
theorem claim_6_2_4 :
    ∀ (C₀ : ℝ) (c₀ : ℕ), ∃ (C : ℝ) (c : ℕ),
      ∀ (dim : ℕ → ℕ) (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6)
        (vecProg tableProg : Program),
        (∀ h : ℕ, 3 ≤ h → IsMVFamily (2 ^ h) (dim h) (u h) (v h)) →
        MVComputable dim u v C₀ c₀ vecProg tableProg →
        ∃ (I : OCHPImpl (actFamily dim u v)) (hintProg : Program),
          Deterministic hintProg ∧
          ∀ h : ℕ, 3 ≤ h →
            (Function.Injective (I.encKey (2 ^ h)) ∧
              ∀ K, (I.encKey (2 ^ h) K).length = (h + 1) * dim h) ∧
            (Function.Injective (I.encHint (2 ^ h)) ∧
              ∀ z, (I.encHint (2 ^ h) z).length = 2 * dim h) ∧
            (Function.Injective (I.encAns (2 ^ h)) ∧
              ∀ a, (I.encAns (2 ^ h) a).length = 2 * dim h) ∧
            I.Efficient (2 ^ h) (C * h * dim h) (C * dim h * (h : ℝ) ^ c) (C * h * dim h)
              (C * h * dim h) (C * 2 ^ h * dim h * (h : ℝ) ^ c) ((h + 1) * dim h) (2 * dim h) ∧
            ∀ (D : Fin (2 ^ h * 2 ^ h) → Bool) (K : (actFamily dim u v (2 ^ h)).Key),
              let inp := encNat (2 ^ h) ++ encBits (I.encKey (2 ^ h) K) ++ List.ofFn D
              Halts hintProg inp zeroTape ∧
              output hintProg inp zeroTape =
                I.encHint (2 ^ h) ((actFamily dim u v (2 ^ h)).hint D K) ∧
              (cost hintProg inp zeroTape : ℝ) ≤ C * 2 ^ h * dim h * (h : ℝ) ^ c := by sorry

end ITPIRPreproc.MatchVec
