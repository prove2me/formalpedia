-- Prove2me | Theorems.Thm_OnlineGND_lemma_2
-- name    : OnlineGND.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:22:51.812235+00:00
-- url     : https://prove2.me/theorems/8aea983a-a452-4bc7-8185-f43578ca3955
-- title:
--   Lemma 2 — weak duality between (P) and (D)
-- statement:
--   Consider GND with weighted power costs $c_ex^{\alpha_e}$, $c_e\ge0$, $\alpha_e\ge1$, and weights $w_{i,e}\ge0$; let $E_1=\{e:\alpha_e=1\}$ and $\beta_e=\alpha_e/(\alpha_e-1)$ for $e\notin E_1$. For any feasible primal solution $x$ of (P) (that is, $x\ge0$ and $\sum_{p\in\mathcal P_i}x_{i,p}\ge1$ for all $i$) and any feasible dual solution $(y,z)$ of (D),
--   $$\sum_{e\in E}c_e\Bigl(\sum_{i=1}^Nw_{i,e}\sum_{p\in\mathcal P_i:e\in p}x_{i,p}\Bigr)^{\alpha_e}\ \ge\ \sum_{i=1}^Ny_i-\sum_{e\in E\setminus E_1}\frac{c_e\alpha_e}{\beta_e}\,z_e^{\beta_e}.$$
--
--   Weak duality turns every feasible dual solution into a lower bound on the optimum, which is how the dual-fitting proofs of Theorems 4–6 bound the optimum.
--
--   Differences from the source:
--   - generalization: GND weights $w_{i,e}\ge1$ → $w_{i,e}\ge0$; reason: Theorem 6 applies the lemma to (D″), whose dummy weights $c_e\alpha_ee^{-\alpha}w_{i,e}^{\alpha_e}$ can be below $1$; every instance with $w\ge1$ is covered
--   - encoding: $x\ge0$ → $x_{i,p}\ge0$ for $p\in\mathcal P_i$; reason: only these variables exist in (P)
-- source:
--   Nagarajan & Wang, Online Generalized Network Design Under (Dis)Economies of Scale, arXiv:2007.07721v1, Lemma 2, pp.7–8; (P), (D) p.7

import Definitions.Def_OnlineGND_Relaxation

namespace OnlineGND

/-- **Lemma 2** (Nagarajan & Wang, arXiv:2007.07721v1, §3, pp.7–8), weak duality for (P) and (D):
for any primal `x ∈ (P)` and dual `(y, z) ∈ (D)`,
`Σ_{e∈E} cₑ (Σᵢ w_{i,e} Σ_{p∈𝒫ᵢ:e∈p} x_{i,p})^{αₑ} ≥ Σᵢ yᵢ − Σ_{e∈E∖E₁} (cₑαₑ/βₑ) zₑ^{βₑ}`.

**Formalization Note.** Weighted power costs with `cₑ ≥ 0`, `αₑ ≥ 1`. Weights are only assumed
`w_{i,e} ≥ 0` (the paper's GND has `w ≥ 1`); Theorem 6's proof applies the lemma to the program (D″)
whose dummy weights `cₑαₑe^{−α}w_{i,e}^{αₑ}` may be below `1`. -/
theorem lemma_2 {E : Type*} [Fintype E] [DecidableEq E] {N : ℕ} (c α : E → ℝ)
    (hc : ∀ e, 0 ≤ c e) (hα : ∀ e, 1 ≤ α e) (reqs : Fin N → Request E)
    (hw : ∀ i e, 0 ≤ (reqs i).w e) (x : Fin N → Finset E → ℝ) (hx : IsPrimalFeasible reqs x)
    (y : Fin N → ℝ) (z : E → ℝ) (hyz : IsDualFeasible c α reqs y z) :
    dualObj c α y z ≤ primalObj c α reqs x := by sorry

end OnlineGND
