-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_Torsor_forward_pullback
-- name    : OAI.ComplexCancellation.Torsor.forward_pullback
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:14:15.710817+00:00
-- url     : https://prove2.me/theorems/c2be6a85-8da2-4ba5-85a5-0c8619965a91
-- title:
--   The frame embedding of the bundle ring is compatible with the pullback from $G$
-- statement:
--   Let $G = \mathbb{C}[p,s,u,F,J]/(H_0)$, where $x = s^2 + u^3 + p^2F$ and $H_0 = x^2F - (1 + 2sx)J - p^2J^2$; thus $G$ is obtained from the hypersurface ring $A = \mathbb{C}[p,s,u,F,J]/\big(x^2F - (1+2sx)J - p^2J^2 - pu\big)$ with $x = s^2 + u^3 + p^2F$ by dropping the term $-pu$ from the defining equation. In $G$ put $y = s + x(x - u^3)$ and $z = sx + p^2J$; then $xy = z(z+1)$ holds in $G$.
--
--   Let $S = \mathbb{C}[a,b,c,d,u]/(ac - bd - 1)$, let $v = a^3b - a^2u^3 - d^2 \in S$, and let $B = S[\tau,V]/(\tau^2V - v)$ (the bundle ring), with $S$ identified with its image in $B$. Let $\psi : G \to B$ be the $\mathbb{C}$-algebra homomorphism (the pullback) determined by $\psi(p) = \tau$, $\psi(s) = dc - ab(ab - u^3)$, $\psi(u) = u$, $\psi(F) = C_1V$ and $\psi(J) = b^2V$, where $C_1 = c^2 - b^2(ab - u^3)$.
--
--   Now let $P$ be a commutative $\mathbb{C}$-algebra that is an integral domain, and let $\rho : G \to P$ be an injective $\mathbb{C}$-algebra homomorphism. A frame $Q$ for $\rho$ consists of elements $a_0, b_0, c_0, d_0 \in P$ with
--   $$
--   a_0b_0 = \rho(x),\qquad d_0c_0 = \rho(y),\qquad d_0b_0 = \rho(z),\qquad a_0c_0 - d_0b_0 = 1 .
--   $$
--   Let $L = P[T, T^{-1}]$ be the Laurent polynomial ring over $P$, and let $\sigma_Q : S \to L$ be the $\mathbb{C}$-algebra homomorphism with $a \mapsto a_0T$, $d \mapsto d_0T$, $b \mapsto b_0T^{-1}$, $c \mapsto c_0T^{-1}$ and $u \mapsto \rho(u)$ (well defined because $a_0c_0 - d_0b_0 = 1$). It extends to the $\mathbb{C}$-algebra homomorphism $\Phi_Q : B \to L$ with $\Phi_Q(\tau) = \rho(p)$ and $\Phi_Q(V) = \sigma_Q(\alpha)\rho(F) + \sigma_Q(\beta)\rho(J)$, where $\alpha = a^2(1 - 2bd)$ and $\beta = d^2(3 + 2bd) + \alpha(ab - u^3)$; this is well defined because $\rho(p)^2\,\Phi_Q(V) = \sigma_Q(v)$.
--
--   Then $\Phi_Q$ restricts to $\rho$ on the image of $\psi$: for every $r \in G$,
--
--   $$
--   \Phi_Q\big(\psi(r)\big) = \rho(r)\qquad\text{(a constant Laurent polynomial)},
--   $$
--   that is, $\Phi_Q \circ \psi$ equals $\rho$ followed by the inclusion of constants $P \hookrightarrow L$.
--
--   Although $\Phi_Q$ sends $a, b, c, d$ to non-constant Laurent monomials, its composite with $\psi$ sees only $\rho$. This is the basic compatibility used when a locally nilpotent derivation of $G$, modelled on $P$ through $\rho$, is lifted to $B$: the lift is computed inside $L$ by differentiating coefficients, and on $\psi(G)$ it then reproduces the original derivation.
--
--   **Formalization Note** In Lean, $G$ is `Degeneration.G`, $S$ is `Determinant.T`, $B$ is `Bundle.B`, $\psi$ is `Bundle.pullback`, a frame is a term of the structure `Frame ρ`, $\sigma_Q$ is `frameMap ρ Q`, $\Phi_Q$ is `forward ρ Q`, and `base ρ` is $\rho$ followed by the constant embedding into `LaurentPolynomial P`. The statement is an equality of $\mathbb{C}$-algebra homomorphisms $G \to L$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/TorsorFrame.lean#L121-L146

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

open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Torsor
open LaurentPolynomial
open MvPolynomial
variable {P : Type*} [CommRing P] [Algebra ℂ P]
variable (ρ : Degeneration.G →ₐ[ℂ] P)
variable (Q : Frame ρ)
variable [IsDomain P]

theorem OAI.ComplexCancellation.Torsor.forward_pullback (hρ : Function.Injective ρ) : (forward ρ Q).comp Bundle.pullback=base ρ := by sorry
