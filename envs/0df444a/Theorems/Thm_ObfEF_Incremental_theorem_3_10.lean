-- Prove2me | Theorems.Thm_ObfEF_Incremental_theorem_3_10
-- name    : ObfEF.Incremental.theorem_3_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:58:30.295717+00:00
-- url     : https://prove2.me/theorems/fd740a78-79db-40de-9c7a-28768eca6f3f
-- title:
--   Theorem 3.10 — a width-three derivation with ≤ K lines yields ≤ c_dK² incremental changes of support ≤ 3 from G_A(C,C') to G_B(C,C')
-- statement:
--   Fix a line-size bound $c_F$ and a block length $c_x\ge1$ for $c_F$ (every formula over $\{\to,\bot\}$ of size at most $c_F$ is computed by the last instruction of a straight-line program of $c_x$ instructions $0,1,\neg a,a\wedge b,a\vee b$). There is a constant $c_d$ such that for all $il,ol,s\ge1$, every power of two $K\ge\max\{2,ol\}$, all circuits $C$ and $C'$ over $B$ with $il$ inputs, $ol$ outputs and size at most $s$, and every derivation of width three for $C$ and $C'$ with at most $K$ lines, each of size at most $c_F$, there are proper configurations
--   $$G_A(C,C')=D_0,\ D_1,\ \dots,\ D_N=G_B(C,C')\quad\text{of } U_{il,ol,s,K},\qquad N\le c_dK^2,$$
--   such that for every $t\in[N]$ some incremental change from $D_{t-1}$ to $D_t$ has a subcircuit of at most $c_d(il+s+K)$ gates, a support of size at most $3$, and describing circuits of size at most $c_d$.
--
--   This is the circuit-side half of the rewriting theorem: with both circuits present in the padding, a short derivation of their equivalence moves every output from the copy of $C$ to the copy of $C'$ through changes that each depend on at most three wire values.
--
--   Differences from the source:
--   - generalization: the paper's constants: c_F of Lemma 3.6 (enlarged on p. 52) and the block length c_x chosen for it → every c_F and every c_x ≥ 1 with SLPBound c_F c_x, with c_d chosen after them; reason: the paper's pair (c_F, c_x) satisfies SLPBound; the proof uses only this property and c_x ≥ 1
--   - reading: a canonical topological order of a circuit (Definitions 2.7, 3.3), not further specified → the order of the circuit's vertex numbering, inputs first (Circuit stores its noninput vertices in a topological order); reason: every circuit of Definition 2.1 is represented once a topological order is fixed, and that order is the canonical one
--   - reading: |φ| is the number of symbols of φ → Fml.size counts each occurrence of a variable, of ⊥ and of → once, parentheses not counted; reason: the paper does not say whether parentheses count; counting them changes sizes by at most a factor 3, absorbed by the constants
--   - encoding: configurations of U_{il,ol,s,K} and proper configurations (Definition 3.3) → Config = CName → Bool (a bit for every constant name; the circuit is labels il ol M cfg over U) and IsProper; reason: a configuration is an assignment to the constant gates; names outside U do not affect the circuit
--   - encoding: 1-based cells, lines i ∈ [K], chain positions t ∈ [K] → 0-based cells in the layout of Pad (cellA … cellF), line block of line i is Y_{i-1}; reason: Lean convention; same topology and configurations
-- source:
--   Abram, Datta, Dutta, Roy, Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to Falsifiable Assumptions, STOC 2027 submission (manuscript sha256 f9518747…), p. 53, Theorem 3.10 (block length c_x: p. 52)

import Mathlib
import Definitions.Def_ObfEF_Incremental_Circuit
import Definitions.Def_ObfEF_Incremental_Formula
import Definitions.Def_ObfEF_Incremental_GateList
import Definitions.Def_ObfEF_Incremental_IncrementalChange
import Definitions.Def_ObfEF_Incremental_Cells
import Definitions.Def_ObfEF_Incremental_Padding
import Definitions.Def_ObfEF_Incremental_Derivation

namespace ObfEF.Incremental

/-- Theorem 3.10 (Incremental Changes from Derivations), for every line-size bound `c_F` and every
block length `c_x ≥ 1` with the straight-line-program property of p. 52. There is a constant `c_d`
such that for all `il, ol, s ≥ 1`, every power of two `K ≥ max {2, ol}`, all circuits `C, C'` over
`B` with `il` inputs, `ol` outputs and size at most `s`, and every derivation of width three for
`C` and `C'` with at most `K` lines, each of size at most `c_F`, there are proper configurations
`G_A(C, C') = D₀, D₁, …, D_N = G_B(C, C')` of `U_{il,ol,s,K}` with `N ≤ c_d K²` such that for every
`t ∈ [N]` some incremental change from `D_{t-1}` to `D_t` has a subcircuit of at most
`c_d(il + s + K)` gates, a support of size at most 3, and circuits of size at most `c_d`. -/
theorem theorem_3_10 (cF cx : ℕ) (hcx : 1 ≤ cx) (hslp : SLPBound cF cx) :
    ∃ cd : ℕ, ∀ (il ol s K : ℕ), 1 ≤ il → 1 ≤ ol → 1 ≤ s →
      (∃ m : ℕ, K = 2 ^ m) → 2 ≤ K → ol ≤ K →
      ∀ (C C' : Circuit (Fin il) ol), C.size ≤ s → C'.size ≤ s →
      ∀ θ : List Fml, IsDerivationW3 C C' θ → θ.length ≤ K → (∀ φ ∈ θ, φ.size ≤ cF) →
      ∃ N : ℕ, N ≤ cd * K ^ 2 ∧ ∃ D : Fin (N + 1) → Config,
        (∀ t, IsProper il ol (Pad.M cx ol s K) (D t)) ∧
        D 0 = GA cx il ol s K C (some C') ∧ D (Fin.last N) = GB cx il ol s K (some C) C' ∧
        ∀ t : Fin N,
          ∃ ch : IncrementalChange (UPad cx il ol s K)
              (labels il ol (Pad.M cx ol s K) (D t.castSucc))
              (labels il ol (Pad.M cx ol s K) (D t.succ)),
            ch.S.card ≤ cd * (il + s + K) ∧ ch.R.card ≤ 3 ∧
            ∀ j ∈ ch.S, (ch.Γ j).size ≤ cd ∧ (ch.Γ' j).size ≤ cd := by sorry

end ObfEF.Incremental
