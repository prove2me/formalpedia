-- Prove2me | Theorems.Thm_MasulloGRH_strongDual_barrelledSpace_of_semiReflexive
-- name    : MasulloGRH.strongDual_barrelledSpace_of_semiReflexive
-- status  : Proved
-- author  : @Miikka
-- created : 2026-11-21T09:49:01.851194+00:00
-- url     : https://prove2.me/theorems/fd7d49b6-ffce-43ef-834f-49fcafcd6a4f
-- title:
--   The strong dual of a semi-reflexive space is barrelled
-- statement:
--   Let $E$ be a complex Hausdorff locally convex space which is **semi-reflexive**: every continuous linear functional $\varphi$ on the strong dual $E'_\beta$ is the evaluation $f\mapsto f(x)$ at a unique $x\in E$.
--
--   Then $E'_\beta$ is **barrelled** (`BarrelledSpace ℂ (StrongDual ℂ E)`): every lower semicontinuous seminorm on $E'_\beta$ is continuous.
--
--   This is one of the ingredients of Theorem D.1.5.7 (Main Structure Theorem on Schwartz–Bruhat spaces).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Example C.1.4.6(3), used in the proof of Theorem D.1.5.7 ('In particular, S(G)'_β is barrelled'), pp. 763–764; Schaefer, Topological Vector Spaces, IV.5.6

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strongDual_barrelledSpace_of_semiReflexive (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E)
    (hr : ∀ φ : StrongDual ℂ (StrongDual ℂ E), ∃! x : E, ∀ f : StrongDual ℂ E, φ f = f x) :
    BarrelledSpace ℂ (StrongDual ℂ E) := by sorry

end MasulloGRH
