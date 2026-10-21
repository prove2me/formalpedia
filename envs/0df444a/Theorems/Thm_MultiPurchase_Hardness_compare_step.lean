-- Prove2me | Theorems.Thm_MultiPurchase_Hardness_compare_step
-- name    : MultiPurchase.Hardness.compare_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:21:58.790201+00:00
-- url     : https://prove2.me/theorems/aa4203b7-98fd-48e5-9417-b24fa2c2b3c0
-- title:
--   Proof of Theorem 1, App. p. 4 (Compare-Step) — max R₂(C) ≥ κ iff max ΣΣ θij x_i x_j (r̂ij − κ) ≥ κ v0
-- statement:
--   Consider a well-formed BundleMVL-2 instance (revenues $r_i>0$, weights $V\ge 0$, no-purchase weight $v_0>0$) with $\theta_{ij}$, $\hat r_{ij}$ and $x^C_i$ as in eq. (4), and let $\kappa$ be any rational threshold. Then
--
--   $$\max_{C\in 2^W}R_2(C)\ge\kappa\iff\max_{C\in 2^W}\sum_{i\in W}\sum_{j\in W}\theta_{ij}x^C_ix^C_j(\hat r_{ij}-\kappa)\ge\kappa v_0 .$$
--
--   In words: some recommendation set has expected revenue at least $\kappa$ if and only if some recommendation set makes the quadratic form on the right at least $\kappa v_0$.
--
--   This is the comparison step of the paper's binary-search algorithm (eq. (6)) and the decision problem the hardness proof reduces Max-Cut to.
--
--   **Formalization Note** Both maxima are over the finite family $2^W$, so "max $\ge$" is stated as "there exists $C$ with $\ge$".
-- source:
--   Tulabandhula, Sinha, Karra & Patidar, Multi-Purchase Behavior: Modeling, Estimation and Optimization, arXiv:2006.08055v2, proof of Theorem 1, Appendix p. 4 (PDF 36), display (Compare-Step); also p. 18 (PDF 18), eq. (6)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_MultiPurchase_Hardness_Model

namespace MultiPurchase.Hardness

/-- (Compare-Step), proof of Theorem 1, Appendix p. 4: for a well-formed BundleMVL-2 instance and
any threshold `κ`, `max_{C∈2^W} R₂(C) ≥ κ` iff
`max_{C∈2^W} ∑_{i∈W} ∑_{j∈W} θᵢⱼ x^C_i x^C_j (r̂ᵢⱼ − κ) ≥ κ v0`. -/
theorem compare_step (I : Instance) (hI : I.WellFormed) (kappa : ℚ) :
    (∃ C : Finset (Fin I.n), kappa ≤ I.R2 C) ↔
      ∃ C : Finset (Fin I.n),
        kappa * I.v0 ≤ ∑ i, ∑ j, I.theta i j * xC C i * xC C j * (I.rhat i j - kappa) := by sorry

end MultiPurchase.Hardness
