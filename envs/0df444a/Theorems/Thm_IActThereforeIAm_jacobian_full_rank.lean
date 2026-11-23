-- Prove2me | Theorems.Thm_IActThereforeIAm_jacobian_full_rank
-- name    : IActThereforeIAm.jacobian_full_rank
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:09:49.788169+00:00
-- url     : https://prove2.me/theorems/211e5759-f801-473d-8595-a7a6de4dceb3
-- title:
--   Theorem 3.3, Step I (as proved): the Jacobian of $r=h\circ g$ has full rank everywhere
-- statement:
--   Let the following hold.
--
--   1. $\nu$ is a probability law that charges every nonempty open subset of $\mathbb R^d\times A$ (full support), where $A$ is a topological space with its Borel $\sigma$-algebra. The latent model is valid.
--   2. The conditional densities $p_i$ of $s_{t,i}$ given $(\mathbf s_{t-1},\mathbf a_{t-1})$ exist and are positive, $C^2$ in $s_{t,i}$ and jointly continuous, and Assumption 3.2 holds for them.
--   3. Assumption 3.1 holds: $\mathbf g:\mathbb R^d\to\mathcal X$ is smooth and injective, with $\mathcal X$ a real normed space.
--   4. Every model in the family $\{p_\phi\}$ factorizes as $\prod_jp_{\phi,j}(z_j\mid\mathbf c)$. For $\mathbf z_{t-1}\in(0,1)^d$ and $z_j\in(0,1)$ the factors are positive, $C^2$ in $z_j$ and jointly continuous.
--   5. $\lambda>1$, $\mathbf h:\mathcal X\to(0,1)^d$ is smooth, and $(\mathbf h,\phi)$ is a global minimizer of $\mathcal L_\lambda$ that attains the lower bound $-I(\mathbf s_t;\mathbf s_{t-1},\mathbf a_{t-1})$.
--
--   Then the Jacobian of $\mathbf r=\mathbf h\circ\mathbf g$ has full rank at every latent state:
--
--   $$\operatorname{rank}J_{\mathbf r}(\mathbf s_t)=d\qquad\text{for all }\mathbf s_t\in\mathbb R^d,$$
--
--   so $\mathbf r$ is locally invertible everywhere.
--
--   **Formalization Note** This is the statement the proof in Appendix D establishes, not the printed one. The printed Theorem 3.3 assumes only that $(\mathbf h,\phi)$ is a global minimizer. The proof also uses three facts. First, the minimizer attains the bound $-I(\mathbf s_t;\mathbf s_{t-1},\mathbf a_{t-1})$, through Theorem 2.1. Second, $p_\phi$ factorizes over components (Eq. 47). Third, the density identities (35)-(39) hold pointwise at the actions supplied by Assumption 3.2. The last requires those actions to be charged by the data, which here comes from full support and continuity. Without full support the printed statement is false; a counterexample is in the mission report. Eq. (47) states only the factorization; the regularity of the factors is required only on the encoder range $(0,1)^d$, where the proof differentiates $\log p_\phi$. It cannot be required on all of $\mathbb R^d$: an optimal $p_\phi$ equals $Q_{\mathbf h}$ a.e. and so vanishes a.e. outside $(0,1)^d$. The hypotheses can all hold together: for $d=1$, a finite action set, $s_t=f(a)+\sigma(a)\epsilon$, $\mathbf g=\mathrm{id}$, $\mathbf h$ the CDF of $s_t$ and $p_\phi=Q_{\mathbf h}$ satisfy them. Assumption 3.2 is read with $\mathbf s_{t-1}$ universally quantified, as in its proof. The latent domain is all of $\mathbb R^d$.
-- source:
--   Liu, Huang and Shi, I Act Therefore I Am: When Is JEPA's Action-Conditioning Enough to Learn Causal Mechanisms?, arXiv:2609.31161v1 (2026), Appendix D (proof of Theorem 3.3), Step I, Eqs. (24)-(45), pp. 19-20

import Mathlib
import Definitions.Def_IActThereforeIAm_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace IActThereforeIAm

theorem jacobian_full_rank {d : ℕ} {A X Θ : Type*}
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    (M : LatentSCM d A) (hM : M.IsValid) (hsupp : M.prev.IsOpenPosMeasure)
    (dens : Fin d → (Fin d → ℝ) → A → ℝ → ℝ) (hdens : HasTransitionDensities M dens)
    (hreg : IsRegularDensity dens) (hvar : ActionVariability dens)
    (g : (Fin d → ℝ) → X) (hg : ObsRegular g)
    (lam : ℝ) (hlam : 1 < lam) (model : Θ → (Fin d → ℝ) × A → (Fin d → ℝ) → ℝ)
    (hmodel : ∀ φ, IsRegularFactorizedModel (model φ))
    (h : X → Fin d → ℝ) (hsmooth : ContDiff ℝ ∞ h) (φ : Θ)
    (hmin : IsGlobalMin M g lam model h φ)
    (hattain : ((objective M g lam h (model φ) : ℝ) : EReal) = -((latentInfo M : ℝ≥0∞) : EReal)) :
    ∀ s : Fin d → ℝ, Module.finrank ℝ (LinearMap.range
      (fderiv ℝ (fun y => h (g y)) s : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))) = d := by sorry

end IActThereforeIAm
