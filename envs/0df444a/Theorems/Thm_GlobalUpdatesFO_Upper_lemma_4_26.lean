-- Prove2me | Theorems.Thm_GlobalUpdatesFO_Upper_lemma_4_26
-- name    : GlobalUpdatesFO.Upper.lemma_4_26
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:22:09.877389+00:00
-- url     : https://prove2.me/theorems/b8eee39b-d6a1-4752-9a26-1a5dd1341498
-- title:
--   Lemma 4.26 — a connected component of a disconnected structure of bounded treedepth has strictly smaller first-order index
-- statement:
--   Let $\nu, D \ge 1$, $q \ge \max(3,\nu)$, $\Sigma$ a signature with $\mathrm{maxarity}(\Sigma) \le \nu$, $A$ a disconnected $\Sigma$-structure of treedepth at most $D$ and $C$ a connected component of $A$. Then
--   $$\mu_q(A[C]) < \mu_q(A).$$
--
--   Together with Lemma 4.25 this makes splitting into components pay for itself in the potential.
--
--   **Formalization Note** "Disconnected" is the negation of Mathlib's `SimpleGraph.Connected` for $G(A)$; since a component $C$ is given, $A$ is nonempty.
--
--   Differences from the source:
--   - encoding: µ_q as a minimum over all finite Σ-structures → foIndex q via structures on Fin m; reason: every finite structure is isomorphic to one on Fin m and full types are isomorphism invariant
--   - encoding: A disconnected; C a connected component; A[C] → ¬ A.gaifman.Connected; C : A.gaifman.ConnectedComponent; A.component C; reason: components of A are those of G(A) (p. 24)
--   - encoding: a finite Σ-structure with universe U(A), relation names of Σ with their arities → Structure σ U on a finite type U : Type, Σ the list of arities, relation names 0, …, |Σ|−1; reason: Lean convention; every finite structure is of this form up to renaming
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), p. 42, Lemma 4.26

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure
import Definitions.Def_GlobalUpdatesFO_Upper_Formula
import Definitions.Def_GlobalUpdatesFO_Upper_Flattening
import Definitions.Def_GlobalUpdatesFO_Upper_Robust

namespace GlobalUpdatesFO.Upper

theorem lemma_4_26 (ν D q : ℕ) (hν : 1 ≤ ν) (hD : 1 ≤ D) (hq : max 3 ν ≤ q)
    (σ : Signature) (hσ : σ.maxarity ≤ ν) (U : Type) [Fintype U] (A : Structure σ U)
    (hdis : ¬ A.gaifman.Connected) (hA : A.td ≤ D) (C : A.gaifman.ConnectedComponent) :
    foIndex q (A.component C) < foIndex q A := by sorry

end GlobalUpdatesFO.Upper
