-- Prove2me | Theorems.Thm_MechanismDesign_IncentiveCompat_ir_lowest_type
-- name    : MechanismDesign.IncentiveCompat.ir_lowest_type
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T02:13:03.752112+00:00
-- url     : https://prove2.me/theorems/b4b4d0d2-2eb7-4251-9774-285e70926bd1
-- title:
--   Proposition 5.9 -- on one-dimensional type spaces, individual rationality reduces to the lowest type
-- statement:
--   Let $R$ be a complete and transitive order of $A$ such that the type set $\Theta$ is one-dimensional with respect to $R$. Assume that there is a lowest type $\underline\theta$ ($\theta \succ_R \underline\theta$ for all $\theta \ne \underline\theta$) and a worst alternative $\underline a$ ($b\,R\,\underline a$ for every $b \ne \underline a$). Then an incentive-compatible direct mechanism $(q,t)$ is individually rational with outside option $\underline a$, i.e. $u(q(\theta),\theta) - t(\theta) \ge u(\underline a,\theta)$ for all $\theta \in \Theta$, if and only if
--   $$u(q(\underline\theta),\underline\theta) - t(\underline\theta) \;\ge\; u(\underline a,\underline\theta).$$
--
--   This generalizes the observation of Chapters 2–4 that only the participation constraint of the lowest type binds.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, p.110, Proposition 5.9, Definition 5.11

import Mathlib
import Definitions.Def_MechanismDesign_IncentiveCompat_Model

namespace MechanismDesign.IncentiveCompat

/-- Proposition 5.9 (p.110). Let `R` be a complete and transitive order of `A` with `Θ`
one-dimensional with respect to `R`; let `θlo` be the lowest type (`θ ≻_R θlo` for every
`θ ≠ θlo`) and `alo` the worst alternative (`b R alo` for every `b ≠ alo`). Then an
incentive-compatible direct mechanism is individually rational with outside option `alo` if and
only if `u(q(θlo), θlo) - t(θlo) ≥ u(alo, θlo)`. -/
theorem ir_lowest_type {A Θ : Type*} [Nonempty Θ] (u : A → Θ → ℝ) (R : A → A → Prop)
    (hR : IsCompleteTransitive R) (h1 : OneDimensional u R) (θlo : Θ)
    (hθlo : ∀ θ : Θ, θ ≠ θlo → HigherType u R θ θlo) (alo : A)
    (halo : ∀ b : A, b ≠ alo → R b alo) (M : DirectMechanism A Θ) (hIC : IsIC u M) :
    IsIRWith u M alo ↔ u alo θlo ≤ u (M.q θlo) θlo - M.t θlo := by sorry

end MechanismDesign.IncentiveCompat
