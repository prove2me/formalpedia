-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_lemma_6_2
-- name    : ITPIRPreproc.MatchVec.lemma_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:12:22.1884+00:00
-- url     : https://prove2.me/theorems/8a5c15da-fbd5-4fc8-9b0e-04b2674c1ee3
-- title:
--   Lemma 6.2 — the matching-vector primitive with activation bits satisfies Definition 4.1 with recovery probability 1/2 and the §4.1 efficiency requirements
-- statement:
--   Let the matching vectors $u_a,v_a$ ($m=2^h$ rows, dimension $d=\dim(h)$) satisfy (7) with distinct $v_a\bmod2$ and be computable with constants $C_0,c_0$. Then:
--
--   1. for every $h\ge3$, the construction of §6.2 on databases of length $n=m^2$ satisfies Definition 4.1, with recovery probability exactly $1/2$ for every database and every index;
--   2. there are constants $C,c$ depending only on $C_0,c_0$, and an implementation (the same programs for all $h$), such that for every $h\ge3$: keys and queries have $(h+1)d$ bits and hints and answers $2d$ bits; its running times satisfy
--   $$\mathrm{time}(\mathsf{Query})=O(hd),\quad \mathrm{time}(\mathsf{Decode})=O(hd),\quad \mathrm{time}(\mathsf{Hint})=md\,\mathrm{poly}(h),\quad \mathrm{time}(\mathsf{Answer})=md\,\mathrm{poly}(h);$$
--   and the efficiency requirements of §4.1 hold with $t_{\rm basic}(n)=O(hd)$ and $t_{\rm stream}(n)=d\,\mathrm{poly}(h)$: for every $L\ge E$, streaming initialization, work per chunk and total client storage are at most $L\,t_{\rm stream}(n)$, including the vector tables and the temporary workspace.
--
--   All bounds are worst-case, with $O(hd)=C\,h\,d$, $md\,\mathrm{poly}(h)=C\,m\,d\,h^c$ and $d\,\mathrm{poly}(h)=C\,d\,h^c$. This is the primitive to which Lemma 4.2 is applied in the proof of Theorem 6.1.
--
--   **Formalization Note** In the interface of Definition 4.1, positions of $[m]\times[m]$ are numbered row-major, and the decoded $\mathbb F_3$ value $2$ (which never occurs on compatible keys) is reported as $\bot$.
--
--   Differences from the source:
--   - reading: the construction's running times, sizes and streaming bounds → existence of word-RAM programs (and injective bit codes) implementing the defined algorithms (14)–(17) and the streaming hint computation within the stated worst-case bounds; reason: the paper describes its algorithms in prose; a running time is a property of an implementation in the RAM model of §3
--   - reading: O(hd), md poly(h), d poly(h) → C·h·d, C·m·d·h^c, C·d·h^c with C, c depending only on the constants C₀, c₀ with which the matching vectors are computable; reason: O(·) and poly(·) as constants chosen before h, the family and the programs; the matching vectors' own computation cost is the only input they can depend on
--   - generalization: the construction with the matching vectors of §5.2 (Appendix A) → the construction with every matching-vector family that satisfies (7) with distinct v_a mod 2 and is computable with constants C₀, c₀; one implementation for all h ≥ 3; reason: the §5.2 family is such a family (the matching_vectors_eq7 milestone), so the statement specializes to the paper's
--   - encoding: the client retains both vector tables; storage includes the vector tables → the vector tables are the implementation's public table, given to the client programs and charged to the streaming budget E·t_stream; reason: §6.2 and Claim 6.2.4 count the tables in the streaming initialization and storage
--   - encoding: time(A) is the worst-case bit work, including input and output processing → each time bound also bounds the length of the program's explicit arguments; outputs are charged by the machine; reason: the definition of time(·) on p.14
--   - encoding: E = m/8 consecutive chunks of 8m bits; streaming algorithm → E = ⌊m/8⌋ chunks of ⌈n/E⌉ = 8m bits, the streaming algorithm as an initialization program and a per-chunk program with a bit-string state; reason: for m = 2^h ≥ 8 the chunk length is exactly 8m; a suspended streaming computation is its state
--   - encoding: positions (a, b) ∈ [m] × F₂^h; decoded value in F₃ ∪ {⊥} → row-major indices of Fin (m·m); F₃ values 0, 1 read as bits and 2 as ⊥; reason: the generic interface of Definition 4.1 indexes [n] and outputs {0,1} ∪ {⊥}; the value 2 never arises on compatible keys
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), Lemma 6.2, printed p.21 (PDF p.23)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_ActivationPrimitive
import Definitions.Def_ITPIRPreproc_MatchVec_Efficiency

open scoped ENNReal

namespace ITPIRPreproc.MatchVec

open WordRAM

/-- Lemma 6.2, printed p.21 (PDF p.23). For a matching-vector family (7) with distinct
`v_a mod 2`, computable with constants `C₀, c₀`, the §6.2 construction (`m = 2^h`, `h ≥ 3`,
`n = m²`) satisfies Definition 4.1 with recovery probability exactly `1/2`; and, with constants
`C, c` depending only on `C₀, c₀`, it has an implementation with `(h+1)d`-bit keys and queries,
`2d`-bit hints and answers, `time(Query) = O(hd)`, `time(Decode) = O(hd)`,
`time(Hint) = md·poly(h)`, `time(Answer) = md·poly(h)`, and the efficiency requirements of §4.1
with `t_basic = O(hd)` and `t_stream = d·poly(h)` (streaming initialization, work per chunk and
total storage at most `L·t_stream` for every `L ≥ E`, tables and workspace included). -/
theorem lemma_6_2 :
    ∀ (C₀ : ℝ) (c₀ : ℕ), ∃ (C : ℝ) (c : ℕ),
      ∀ (dim : ℕ → ℕ) (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6)
        (vecProg tableProg : Program),
        (∀ h : ℕ, 3 ≤ h → IsMVFamily (2 ^ h) (dim h) (u h) (v h)) →
        MVComputable dim u v C₀ c₀ vecProg tableProg →
        (∀ h : ℕ, 3 ≤ h →
          (actFamily dim u v (2 ^ h)).IsOneCompatibleHint (2 ^ h) ∧
          ∀ (D : Fin (2 ^ h * 2 ^ h) → Bool) (i : Fin (2 ^ h * 2 ^ h)),
            (actFamily dim u v (2 ^ h)).probRecover D i = 2⁻¹) ∧
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
