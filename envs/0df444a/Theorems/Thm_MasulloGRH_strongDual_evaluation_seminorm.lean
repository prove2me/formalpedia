-- Prove2me | Theorems.Thm_MasulloGRH_strongDual_evaluation_seminorm
-- name    : MasulloGRH.strongDual_evaluation_seminorm
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:12:34.712111+00:00
-- url     : https://prove2.me/theorems/898f4723-574b-4a57-acae-35f591c5c460
-- title:
--   Evaluations along a bounded sequence are equicontinuous on the strong dual
-- statement:
--   Let $E$ be a Hausdorff locally convex space over $\mathbb C$ and $(y_n)_{n\ge0}$ a bounded sequence in $E$. Then each evaluation $\varphi_n : f\mapsto f(y_n)$ is a continuous linear functional on the strong dual $E'_\beta$, and there is a continuous seminorm $q$ on $E'_\beta$ with $|f(y_n)|\le q(f)$ for all $n$ and all $f\in E'$ (e.g. $q(f)=\sup_n|f(y_n)|$, the gauge of the polar of the bounded set $\{y_n\}$).
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix C, §C.2.4 (nuclearity of the strong dual of a nuclear Fréchet space); cf. Schaefer, Topological Vector Spaces, III.7 and IV.9.6; Pietsch, Nuclear Locally Convex Spaces, 4.4

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strongDual_evaluation_seminorm (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E)
    (y : ℕ → E) (hy : Bornology.IsVonNBounded ℂ (Set.range y)) :
    ∃ (q : Seminorm ℂ (StrongDual ℂ E)) (φ : ℕ → StrongDual ℂ (StrongDual ℂ E)),
      Continuous q ∧ (∀ n f, φ n f = f (y n)) ∧ ∀ n (f : StrongDual ℂ E), ‖f (y n)‖ ≤ q f := by sorry

end MasulloGRH
