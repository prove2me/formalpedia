-- Prove2me | Theorems.Thm_InfoDerivQT_atomicity_of_composition
-- name    : InfoDerivQT.atomicity_of_composition
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T11:13:28.812023+00:00
-- url     : https://prove2.me/theorems/5732722f-bcda-4d82-835f-3a366a40d3ce
-- title:
--   Lemma 16 — the composition of two atomic transformations is atomic
-- statement:
--   Let $T$ satisfy the six principles and let $A,B,C$ be systems. If $\mathcal C\in\mathrm{Transf}(A,B)$ and $\mathcal D\in\mathrm{Transf}(B,C)$ are atomic, then the sequential composition $\mathcal D\mathcal C\in\mathrm{Transf}(A,C)$ is atomic.
--
--   This is Axiom 5$'$ of the paper; it is derived here from pure conditioning and purification and is used repeatedly afterwards.
-- source:
--   G. Chiribella, G. M. D'Ariano, P. Perinotti, *Informational derivation of quantum theory*, Phys. Rev. A 84, 012311 (2011), https://doi.org/10.1103/PhysRevA.84.012311 (arXiv:1011.6451), p. 012311-12, Sec. IV D, Lemma 16 (Atomicity of composition)

import Mathlib
import Definitions.Def_InfoDerivQT_principles

namespace InfoDerivQT
theorem atomicity_of_composition (T : OPT) (hT : T.SatisfiesPrinciples) (A B C : T.Sys)
    (D₁ : Vec (T.size A) →ₗ[ℝ] Vec (T.size B)) (D₂ : Vec (T.size B) →ₗ[ℝ] Vec (T.size C))
    (h₁ : T.IsAtomicT A B D₁) (h₂ : T.IsAtomicT B C D₂) :
    T.IsAtomicT A C (D₂.comp D₁) := by sorry
end InfoDerivQT
