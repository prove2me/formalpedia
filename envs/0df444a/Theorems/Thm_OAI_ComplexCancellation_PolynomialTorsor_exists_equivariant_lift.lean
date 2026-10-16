-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_PolynomialTorsor_exists_equivariant_lift
-- name    : OAI.ComplexCancellation.PolynomialTorsor.exists_equivariant_lift
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:25:09.726237+00:00
-- url     : https://prove2.me/theorems/680ff94c-1a0d-4e82-b3b7-305f7b692f56
-- title:
--   Lifting locally nilpotent derivations of $G$ to Euler-equivariant ones on the bundle ring
-- statement:
--   Let $G = \mathbb{C}[p,s,u,F,J]/(H_0)$, where $x = s^2 + u^3 + p^2F$ and $H_0 = x^2F - (1 + 2sx)J - p^2J^2$; thus $G$ is obtained from the hypersurface ring $A = \mathbb{C}[p,s,u,F,J]/\big(x^2F - (1+2sx)J - p^2J^2 - pu\big)$ with $x = s^2 + u^3 + p^2F$ by dropping the term $-pu$ from the defining equation. Let $S = \mathbb{C}[a,b,c,d,u]/(ac - bd - 1)$, let $v = a^3b - a^2u^3 - d^2 \in S$, and let $B = S[\tau,V]/(\tau^2V - v)$ (the bundle ring), with $S$ identified with its image in $B$. Let $\psi : G \to B$ be the $\mathbb{C}$-algebra homomorphism (the pullback) determined by $\psi(p) = \tau$, $\psi(s) = dc - ab(ab - u^3)$, $\psi(u) = u$, $\psi(F) = C_1V$ and $\psi(J) = b^2V$, where $C_1 = c^2 - b^2(ab - u^3)$.
--
--   Let $\varepsilon$ be the Euler derivation of $S$, i.e. the $\mathbb{C}$-derivation with $\varepsilon(a) = a$, $\varepsilon(d) = d$, $\varepsilon(b) = -b$, $\varepsilon(c) = -c$ and $\varepsilon(u) = 0$; it satisfies $\varepsilon(v) = 2v$. The fiber Euler derivation $\hat\varepsilon$ of $B$ is the $\mathbb{C}$-derivation that agrees with $\varepsilon$ on $S$ and satisfies $\hat\varepsilon(\tau) = 0$ and $\hat\varepsilon(V) = 2V$ (it is well defined because it sends $\tau^2V - v$ to $2(\tau^2V - v)$). A derivation is called locally nilpotent if every element is killed by some iterate of it.
--
--   Let $D$ be a nonzero locally nilpotent $\mathbb{C}$-derivation of $G$. Then there exist $c \in G$ with $c \neq 0$ and a nonzero locally nilpotent $\mathbb{C}$-derivation $E$ of $B$ such that
--
--   $$
--   E\big(\psi(r)\big) = \psi\big(c\,D(r)\big)\ \ \text{for all } r \in G, \qquad \hat\varepsilon\big(E(b)\big) = E\big(\hat\varepsilon(b)\big)\ \ \text{for all } b \in B .
--   $$
--
--   Thus every nonzero locally nilpotent derivation of $G$, after multiplication by a nonzero element $c$, lifts along $\psi$ to a nonzero locally nilpotent derivation of $B$ that commutes with the fiber Euler derivation. In the proof that $A$ is not a polynomial ring in four variables, a hypothetical isomorphism $A \cong \mathbb{C}[X_1,\dots,X_4]$ produces such a $D$ together with a nonzero homogeneous element of positive degree in its kernel; the lift $E$ then kills the image of that element under $\psi$, and a positive-degree obstruction on $B$ gives a contradiction.
--
--   **Formalization Note** $G$ is `Degeneration.G`, $B$ is `Bundle.B`, $\psi$ is `Bundle.pullback`, $\hat\varepsilon$ is `Bundle.fiberEuler`, and local nilpotence is `LND.LocallyNilpotent`. About the multiplier $c$ the statement records only $c \neq 0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/EquivariantLift.lean#L10-L49

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

open OAI OAI.ComplexCancellation OAI.ComplexCancellation.PolynomialTorsor
open PolynomialModel

theorem OAI.ComplexCancellation.PolynomialTorsor.exists_equivariant_lift (D : Derivation ℂ Degeneration.G Degeneration.G)
    (hD : LND.LocallyNilpotent D) (hDn : D ≠ 0) :
    ∃ (c : Degeneration.G) (E : Derivation ℂ Bundle.B Bundle.B),
      c ≠ 0 ∧ LND.LocallyNilpotent E ∧ E ≠ 0 ∧
      (∀ r, E (Bundle.pullback r)=Bundle.pullback (c*D r)) ∧
      ∀ b, Bundle.fiberEuler (E b)=E (Bundle.fiberEuler b) := by sorry
