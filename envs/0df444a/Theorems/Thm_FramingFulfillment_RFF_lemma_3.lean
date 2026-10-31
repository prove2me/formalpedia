-- Prove2me | Theorems.Thm_FramingFulfillment_RFF_lemma_3
-- name    : FramingFulfillment.RFF.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:42.883719+00:00
-- url     : https://prove2.me/theorems/80f25dff-79b9-4337-a23f-6641f08120e5
-- title:
--   Lemma 3, p. 16 — the re-scaled distribution ρ of ConstrDist satisfies (7a)–(7c)
-- statement:
--   Fix a region $j$ and a fractional framing $x\in[0,1]^{I\times R}$ satisfying (10a) $\sum_i x_{ir}\le Q_r$ and (10b) $\sum_r x_{ir}=1$. Fix any framing decomposition $B=\sum_\ell\alpha_\ell B^{(\ell)}$ of the matrix $B$ of ConstrDist C1(ii), and let $\rho_j$ be the distribution produced by C2–C3. Then
--
--   $$\sum_{\phi\in\Omega(Q)}\rho_j(\phi)=1,\qquad \sum_{\phi\in\Omega(Q)}\rho_j(\phi)\,\theta_{ij}(\phi)=\theta_{ij}(x)\ \ \forall i,\qquad \sum_{\phi\in\Omega(Q)}\rho_j(\phi)\,\mathcal R_{ij}(\phi)=\mathcal R_{ij}(x)\ \ \forall i.$$
--
--   These are conditions (7a)–(7c). Under $\rho_j$, the expected purchase probability and expected revenue of every product match the fluid values of DET'. This identity is the paper's main technical device: the MNL denominators are not linear in the assignment, and the re-scaling step C3 corrects for that.
--
--   **Formalization Note** The page states Lemma 3 for the base model, without a region index. §5 applies it to each region $j$ with region $j$'s attractions, and it is stated that way here. It holds for every framing decomposition, not only the one the paper's algorithm produces.
-- source:
--   Lei, Jasin, Uichanco & Vakhutinsky, Joint Product Framing and Order Fulfillment under the MNL Model, SSRN 3282019 (PDF sha256 7d6bd797…), p. 16, Lemma 3; conditions (7a)–(7c), p. 12; ConstrDist, pp. 15–16

import Mathlib
import Definitions.Def_FramingFulfillment_RFF_Model

namespace FramingFulfillment.RFF

open Finset

/-- Lemma 3 (p. 16), region by region as in §5: for a framing `x` of region `j` satisfying
(10a), (10b), (10e) and any framing decomposition of `B(x)`, the re-scaled distribution `ρ` of
ConstrDist satisfies (7a)–(7c). -/
theorem lemma_3 (P : Inst) (hP : P.Standing) (j : Fin P.J) (x : Fin P.I → Fin P.R → ℝ)
    (h10a : ∀ r, ∑ i, x i r ≤ (P.Q r : ℝ)) (h10b : ∀ i, ∑ r, x i r = 1)
    (h10e : ∀ i r, 0 ≤ x i r ∧ x i r ≤ 1) (d : FramingDecomp x) :
    (∑ φ ∈ P.Omega, P.rho j d φ = 1) ∧
    (∀ i, ∑ φ ∈ P.Omega, P.rho j d φ * P.thetaPhi j φ i = P.thetaX j x i) ∧
    (∀ i, ∑ φ ∈ P.Omega, P.rho j d φ * P.revPhi j φ i = P.revX j x i) := by sorry

end FramingFulfillment.RFF
