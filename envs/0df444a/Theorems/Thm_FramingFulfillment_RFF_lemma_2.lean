-- Prove2me | Theorems.Thm_FramingFulfillment_RFF_lemma_2
-- name    : FramingFulfillment.RFF.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:38.91259+00:00
-- url     : https://prove2.me/theorems/f207704c-a06a-4564-ae05-bd8e58eeb46b
-- title:
--   Lemma 2, p. 16 — the matrix B of ConstrDist C1(ii) is a framing matrix; integral framing matrices give unique feasible assignments
-- statement:
--   Fix one region and one period, and let $x=(x_{ir})\in[0,1]^{I\times R}$ satisfy the DET' constraints (10a) $\sum_i x_{ir}\le Q_r$ and (10b) $\sum_r x_{ir}=1$. Let $q_r=\sum_i x_{ir}$, $\tilde Q_r=\lceil q_r\rceil$ and $\tilde I=\sum_r\lceil q_r\rceil-I$. Let $B$ be the $(I+\tilde I)\times R$ matrix of ConstrDist C1(ii): its first $I$ rows are $x$, and each of its $\tilde I$ fictitious rows is $\big((\lceil q_r\rceil-q_r)/\tilde I\big)_r$. Then:
--
--   1. $B$ is a framing matrix with respect to $\tilde Q$, that is,
--   $$\sum_{r}B_{nr}=1\ \ \forall n,\qquad \sum_{n}B_{nr}=\tilde Q_r\ \ \forall r;$$
--   2. for every integral framing matrix $B^{(\ell)}$ with respect to $\tilde Q$, there is exactly one assignment $\phi:[I]\to[R]$ with $\mathbf 1\{\phi(i)=r\}=B^{(\ell)}_{ir}$ for all real products $i\le I$ and all $r$, and this $\phi$ lies in $\Omega(Q)$.
--
--   This is what makes the auxiliary distribution $\tilde\rho$ of ConstrDist a distribution over feasible framing assignments.
--
--   **Formalization Note** The page states Lemma 2 for the base model; §5 applies it to each region's $x^{t,D}_j$, which is how it is stated here. "$\mathbf 1\{\phi(i)=r\}=B^{(\ell)}_{ir}$" is encoded as $\phi(i)=r\iff B^{(\ell)}_{ir}=1$, which is equivalent for a 0/1 matrix.
-- source:
--   Lei, Jasin, Uichanco & Vakhutinsky, Joint Product Framing and Order Fulfillment under the MNL Model, SSRN 3282019 (PDF sha256 7d6bd797…), p. 16, Lemma 2 (ConstrDist C1, p. 15)

import Mathlib
import Definitions.Def_FramingFulfillment_RFF_Model

namespace FramingFulfillment.RFF

open Finset

/-- Lemma 2 (p. 16), for the framing `x` of one region and period: the matrix `B(x)` of
ConstrDist C1(ii) is a framing matrix w.r.t. `Q̃`, and every integral framing matrix w.r.t. `Q̃`
determines a unique framing assignment `φ` via `1{φ(i) = r} = B_ir`, which is feasible. -/
theorem lemma_2 (P : Inst) (hP : P.Standing) (x : Fin P.I → Fin P.R → ℝ)
    (h10a : ∀ r, ∑ i, x i r ≤ (P.Q r : ℝ)) (h10b : ∀ i, ∑ r, x i r = 1)
    (h10e : ∀ i r, 0 ≤ x i r ∧ x i r ≤ 1) :
    IsFramingMatrix (Bmat x) (Qtil x) ∧
    ∀ A : Fin (P.I + Itil x) → Fin P.R → ℝ, IsIntegralMatrix A → IsFramingMatrix A (Qtil x) →
      (∃! φ : Fin P.I → Fin P.R, ∀ i r, φ i = r ↔ A (Fin.castAdd (Itil x) i) r = 1) ∧
      ∀ φ : Fin P.I → Fin P.R, (∀ i r, φ i = r ↔ A (Fin.castAdd (Itil x) i) r = 1) →
        φ ∈ P.Omega := by sorry

end FramingFulfillment.RFF
