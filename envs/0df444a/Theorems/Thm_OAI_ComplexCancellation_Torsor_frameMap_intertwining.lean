-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_Torsor_frameMap_intertwining
-- name    : OAI.ComplexCancellation.Torsor.frameMap_intertwining
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:15:45.073294+00:00
-- url     : https://prove2.me/theorems/4299ae71-25fa-4511-b0d1-098c2531c87e
-- title:
--   The frame map intertwines the Euler derivation of $\mathrm{SL}_2\times\mathbb{A}^1$ with $T\,d/dT$
-- statement:
--   Let $G = \mathbb{C}[p,s,u,F,J]/(H_0)$ with $x = s^2 + u^3 + p^2F$ and $H_0 = x^2F - (1+2sx)J - p^2J^2$, and put $y = s + x(x - u^3)$ and $z = sx + p^2J$ in $G$. Let $P$ be any commutative $\mathbb{C}$-algebra, $\rho : G \to P$ a $\mathbb{C}$-algebra homomorphism, and $Q = (a_0, b_0, c_0, d_0)$ a frame for $\rho$, i.e. elements of $P$ with $a_0b_0 = \rho(x)$, $d_0c_0 = \rho(y)$, $d_0b_0 = \rho(z)$ and $a_0c_0 - d_0b_0 = 1$.
--
--   Let $S = \mathbb{C}[a,b,c,d,u]/(ac - bd - 1)$, the coordinate ring of $\mathrm{SL}_2 \times \mathbb{A}^1$, and let $\sigma_Q : S \to P[T, T^{-1}]$ be the $\mathbb{C}$-algebra homomorphism into Laurent polynomials with $a \mapsto a_0T$, $d \mapsto d_0T$, $b \mapsto b_0T^{-1}$, $c \mapsto c_0T^{-1}$ and $u \mapsto \rho(u)$. Let $\varepsilon$ be the Euler derivation of $S$, the $\mathbb{C}$-derivation with $\varepsilon(a) = a$, $\varepsilon(d) = d$, $\varepsilon(b) = -b$, $\varepsilon(c) = -c$ and $\varepsilon(u) = 0$, and let $\theta = T\,\frac{d}{dT}$ be the Euler derivation of $P[T,T^{-1}]$, given by $\theta\big(\sum_n q_nT^n\big) = \sum_n n\,q_nT^n$.
--
--   Then $\sigma_Q$ intertwines $\varepsilon$ and $\theta$: for every $r \in S$,
--
--   $$
--   \theta\big(\sigma_Q(r)\big) = \sigma_Q\big(\varepsilon(r)\big).
--   $$
--
--   The derivation $\varepsilon$ is the infinitesimal generator of the torus action $t \cdot (a,b,c,d,u) = (ta, t^{-1}b, t^{-1}c, td, u)$ and $\theta$ generates $T \mapsto tT$, so the theorem says that $\sigma_Q$ is equivariant at the level of derivations. It is the coefficient part of the statement that the frame embedding of $S[\tau,V]/(\tau^2V - v)$, $v = a^3b - a^2u^3 - d^2$, into $P[T,T^{-1}]$ intertwines the fiber Euler derivation with $\theta$, which is how equivariance of lifted derivations is verified.
--
--   **Formalization Note** $S$ is `Determinant.T`, $\sigma_Q$ is `frameMap ρ Q`, $\theta$ is `LaurentEuler.derivation`, and $\varepsilon$ is `Determinant.Euler`, defined as the commutator $[\delta, \eta]$ of the derivations $\delta$ ($b \mapsto a$, $c \mapsto d$, other generators $\mapsto 0$) and $\eta$ ($a \mapsto b$, $d \mapsto c$, other generators $\mapsto 0$); its values on the generators are the ones listed above. No injectivity or domain hypothesis is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/TorsorEuler.lean#L13-L28

import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_Modification
import Definitions.Def_OAI_Algebra_AffineCancellation_Bundle
import Definitions.Def_OAI_Algebra_AffineCancellation_ModificationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Extraction
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveObstruction
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorFrame
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorInverse
import Definitions.Def_OAI_Algebra_AffineCancellation_ReplicaLift
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentEuler
import Definitions.Def_OAI_Algebra_AffineCancellation_Intertwining

open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Torsor
open LaurentPolynomial
variable {P : Type*} [CommRing P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P) (Q : Frame ρ)

theorem OAI.ComplexCancellation.Torsor.frameMap_intertwining (r : Determinant.T) :
    LaurentEuler.derivation (k := ℂ) (frameMap ρ Q r)=frameMap ρ Q (Determinant.Euler r) := by sorry
