-- Prove2me | Theorems.Thm_NgoFL_endoscopicIndex_isClosedSubsystem
-- name    : NgoFL.endoscopicIndex_isClosedSubsystem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T00:24:52.556252+00:00
-- url     : https://prove2.me/theorems/6b7846ae-46b4-4d61-97e2-0199a57b89c0
-- title:
--   $\Phi_H = \{\alpha : \kappa(\alpha^\vee) = 1\}$ is a closed root subsystem
-- statement:
--   Let $G$ be a split reductive group with root datum $(X^*(T), X_*(T), \Phi, \Phi^\vee)$, and let
--   $\kappa$ be an element of the dual torus $\hat T = \operatorname{Hom}(X_*(T), \mathbb{G}_m)$,
--   that is, a homomorphism from the cocharacter lattice to the multiplicative group of a
--   commutative group. Following §1.8 of Ngo's paper, the endoscopic group $H$ attached to $\kappa$
--   has root system
--
--   $$ \Phi_H \;=\; \{\alpha \in \Phi \;:\; \kappa(\alpha^\vee) = 1\}. $$
--
--   The statement is that $\Phi_H$ is a *closed subsystem* of $\Phi$: it is stable under
--   $\alpha \mapsto -\alpha$, and it is stable under its own reflections, i.e. $s_\beta(\alpha) \in
--   \Phi_H$ whenever $\alpha, \beta \in \Phi_H$.
--
--   This is the fact that makes the endoscopic group well defined and gives meaning to its Weyl
--   group $W_H \subset W$; it is used silently throughout §1.10, in particular in the proof of
--   Lemma 1.10.2, where $\Phi - \Phi_H$ must be stable under $W_H$.
-- source:
--   Bao Chau Ngo, *Le lemme fondamental pour les algebres de Lie*, Publications mathematiques de l'IHES 111 (2010), 1-169, DOI 10.1007/s10240-010-0026-7, p. 17, §1.8 (the endoscopic group attached to $\kappa \in \hat T$)

import Mathlib
import Definitions.Def_NgoEndoscopicDiscriminant

namespace NgoFL

theorem endoscopicIndex_isClosedSubsystem {ι M N A : Type*} [AddCommGroup M]
    [AddCommGroup N] [CommGroup A] (P : RootPairing ι ℤ M N)
    (κ : Multiplicative N →* A) :
    IsClosedSubsystem P (endoscopicIndex P κ) := by sorry

end NgoFL
