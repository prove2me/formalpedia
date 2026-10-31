-- Prove2me | Theorems.Thm_MaxEntSampling_theorem_2
-- name    : MaxEntSampling.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:00:39.702815+00:00
-- url     : https://prove2.me/theorems/13bfeb57-9d3a-48c0-bb37-89da4ac795ab
-- title:
--   Theorem 2 — primal characterization PC (9) of LD (5)
-- statement:
--   Let $V\in\mathbb R^{d\times n}$ have rank $d$, with columns $v_i$, and let $s\in[d]$. The value of the Lagrangian dual LD (5) equals
--
--   $$
--   z^{LD} = \max_x\Bigl\{\Gamma_s\Bigl(\sum_{i\in[n]}x_iv_iv_i^\top\Bigr) : \sum_{i\in[n]}x_i=s,\ x\in[0,1]^n\Bigr\}, \tag{9}
--   $$
--
--   and the maximum is attained at some $x$ in the feasible set $D$.
--
--   Together with Theorem 1 this makes PC (9) a concave relaxation of MESP whose value is at least $z^*$.
--
--   **Formalization Note** Both values are extended reals; LD (5) is the infimum over $\Lambda\succ0$, $\nu\ge0$, $\mu\ge0$.
--
--   Differences from the source:
--   - reading: z^LD := max_x {…} (9) → zLD V s = zPC V s ∧ the supremum zPC is attained at some x ∈ D; reason: the paper writes max and the cited strong-duality theorem (Ben-Tal–Nemirovski, theorem 3.2.2) gives a solvable dual
--   - encoding: extended-real optimal values → EReal (sInf / sSup); reason: Lean convention; same instances
--   - encoding: LD (5) over Λ ⪰ 0, ν, µ ∈ R^n_+ with min → zLD V s, the infimum over Λ ≻ 0, a scalar ν ≥ 0 and µ ∈ ℝⁿ₊; reason: a singular Λ has objective +∞, a free ν gives the same value since v_iᵀΛv_i ≥ 0, and min is the optimal value (see Theorem 1)
--   - encoding: C ⪰ 0 of rank d, C = VᵀV with V ∈ ℝ^{d×n}, and s ≤ d ≤ n → V : Matrix (Fin d) (Fin n) ℝ with V.rank = d and 1 ≤ s ≤ d; reason: C enters only through its factor V; d ≤ n follows from rank V = d ≤ n, so no instance changes
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, Theorem 2, eq. (9), p.9 (PDF p.9)

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model
import Definitions.Def_MaxEntSampling_GammaS
import Definitions.Def_MaxEntSampling_feasD
import Definitions.Def_MaxEntSampling_zLD
import Definitions.Def_MaxEntSampling_zPC

namespace MaxEntSampling

open PropVolSampling.Reduction

/-- **Theorem 2: the primal characterization PC (9) of LD (5).**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, Theorem 2, eq. (9), p.9 (PDF p.9): "LD (5) has the following primal
characterization, i.e., (PC) z^LD := max_x { Γs(Σ_{i∈[n]} xi vi vi^⊤) : Σ_{i∈[n]} xi = s,
x ∈ [0,1]^n }, (9) where function Γs(·) can be found in Definition 2."

Let `V ∈ ℝ^{d×n}` have rank `d` and `s ∈ [d]`. The optimal value of LD (5) equals the supremum of
`Γ_s(Σ_i x_i v_i v_iᵀ)` over `D = {x ∈ [0,1]ⁿ : Σ_i x_i = s}`, and this supremum is attained at
some `x ∈ D`.

**Formalization Note.** Values lie in `EReal`; LD (5) is `zLD` (infimum over `Λ ≻ 0`, `ν ≥ 0`,
`µ ≥ 0`) and PC (9) is `zPC` (supremum over `D`). The "max" of (9) is stated as attainment. The
hypothesis `d ≤ n` of the paper follows from `rank V = d`. -/
theorem theorem_2 {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (s : ℕ) (hs1 : 1 ≤ s) (hsd : s ≤ d)
    (hrank : V.rank = d) :
    zLD V s = zPC V s ∧ ∃ x ∈ feasD n s, GammaS s (weightedGram V x) = zPC V s := by sorry

end MaxEntSampling
