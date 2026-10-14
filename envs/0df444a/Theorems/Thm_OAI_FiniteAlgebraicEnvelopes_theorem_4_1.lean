-- Prove2me | Theorems.Thm_OAI_FiniteAlgebraicEnvelopes_theorem_4_1
-- name    : OAI.FiniteAlgebraicEnvelopes.theorem_4_1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-14T08:27:52.415889+00:00
-- url     : https://prove2.me/theorems/4c0dcf36-3abf-4225-9c0f-aa0f39877f7f
-- title:
--   Theorem 4.1 (annihilating the Steinberg kernel)
-- statement:
--   Let $R$ be a (possibly noncommutative) unital ring, $\psi : R \to R$ an additive multiplicative map, and put $P = \psi(1)$. Suppose $U_0, U_1, V_0, V_1 \in PRP$ each commute with $\psi(R)$ and satisfy $V_iU_j = \delta_{ij}P$ and $U_0V_0 + U_1V_1 = P$. Then the coefficient endomorphism $\theta : x_{ij}(a) \mapsto x_{ij}(\psi(a))$ of $\mathrm{St}_6(R)$ (`steinCoeffMap`) sends every element of the kernel of the matrix representation $\pi : \mathrm{St}_6(R) \to \mathrm{GL}_6(R)$ to the identity.
--
--   This is the preprint's Theorem 4.1 ("annihilating the Steinberg kernel"), the technical heart of Section 4. Its proof puts $E_i = U_iV_i$ ($i=0,1$), and splits $E_0$ further into $E_{00} = U_0U_0V_0V_0$ and $E_{01} = U_0U_1V_1V_0$, each equivalent to $E_1$ via the equation-(17) data $d_v = U_1V_v$, $d_v^* = U_vV_1$. Lemma 4.4, applied with each of $E_0, E_{00}, E_{01}$ against the fixed corner $E_1$, gives $z_{E_0}=z_{E_1}=z_{E_{00}}=z_{E_{01}}$ for $z$ in the kernel; since $E_{00}, E_{01}$ are themselves orthogonal idempotents, the coefficient map decomposes over their sum, giving $z_{E_0} = z_{E_{00}}z_{E_{01}} = z_{E_0}^2$, hence $z_{E_0}=z_{E_1}=1$ by group cancellation. The same decomposition argument applied to $P = E_0+E_1$ then gives $\theta(z) = z_P = z_{E_0}z_{E_1} = 1$.
--
--   **Formalization Note.** As in Lemma 4.4, the preprint's fixed $n=6$ is kept (via `SteinbergGroup 6 R`), matching the source's own three-pair construction. The hypotheses on $\psi$, $P$, $U_i$, $V_i$ are stated explicitly rather than packaged into a structure, following the source's own presentation.
-- source:
--   OpenAI Math Release (2026-09-23), "Finite algebraic envelopes and the Boone-Higman conjecture", Section 4, p. 10, 13 (Theorem 4.1 and its proof)

import Mathlib
import Definitions.Def_BooneHigman_Steinberg
import Definitions.Def_OAI_FiniteAlgebraicEnvelopes_steinCoeffMap

namespace OAI
namespace FiniteAlgebraicEnvelopes

universe u

variable {n : ℕ} {R : Type u} [Ring R]

theorem theorem_4_1 (psi : R → R)
    (hpsi_add : ∀ a b : R, psi (a + b) = psi a + psi b)
    (hpsi_mul : ∀ a b : R, psi (a * b) = psi a * psi b)
    {P U0 U1 V0 V1 : R} (hPdef : P = psi 1) (hU0 : U0 = P * U0 * P) (hU1 : U1 = P * U1 * P)
    (hV0 : V0 = P * V0 * P) (hV1 : V1 = P * V1 * P)
    (hV0U0 : V0 * U0 = P) (hV1U1 : V1 * U1 = P) (hV0U1 : V0 * U1 = 0) (hV1U0 : V1 * U0 = 0)
    (hsum : U0 * V0 + U1 * V1 = P)
    (hU0psi : ∀ c : R, U0 * psi c = psi c * U0) (hU1psi : ∀ c : R, U1 * psi c = psi c * U1)
    (hV0psi : ∀ c : R, V0 * psi c = psi c * V0) (hV1psi : ∀ c : R, V1 * psi c = psi c * V1)
    (z : SteinbergGroup 6 R) (hz : steinPi z = 1) :
    steinCoeffMap psi hpsi_add hpsi_mul z = 1 := by sorry

end FiniteAlgebraicEnvelopes
end OAI
