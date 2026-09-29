-- Prove2me | Theorems.Thm_LewisTorczon_BoundPS_lemma_2_3
-- name    : LewisTorczon.BoundPS.lemma_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:44:01.829074+00:00
-- url     : https://prove2.me/theorems/296cce69-660a-49c9-a80c-bb8a3f1030a5
-- title:
--   Lemma 2.3 — bounded columns give $\Delta_k\ge\psi_*\|s_k^i\|$
-- statement:
--   Let $x_k,\Delta_k,C_k$ be a run of the generalized pattern search method for bound constrained problems with basis matrix $B$, and suppose the columns of the generating matrices are uniformly bounded: there is $C>0$ with $\|c_k^i\|<C$ for all $k$ and all columns $c_k^i$ of $C_k$.
--
--   Then there is a constant $\psi_*>0$, independent of $k$, such that for every trial step $s_k^i=\Delta_k Bc_k^i$,
--   $$\Delta_k\ge\psi_*\,\|s_k^i\| .$$
--
--   Together with Lemma 2.1, the lemma says that $\Delta_k$ and the length of nonzero steps are comparable, so that $\Delta_k\to0$ is equivalent to the steps shrinking to zero.
--
--   **Formalization Note** Norms are Euclidean. The lemma is quoted in the paper from Torczon (1997), Lemma 3.6.
-- source:
--   Lewis & Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report No. 96-20 (NASA CR-198306), March 1996, p. 5, Lemma 2.3 (Lemma 3.6 from [14])

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Lemma 2.3** (Lemma 3.6 of Torczon 1997), p. 5: if the columns of the generating matrices are
uniformly bounded in norm, there is `ψ_* > 0`, independent of `k`, with `Δ_k ≥ ψ_* ‖s_k^i‖` for
every trial step `s_k^i = Δ_k B c_k^i`. -/
theorem lemma_2_3 {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m)
    (hR : IsGPSRun P lo hi f R) (hbdd : BoundedCols R) :
    ∃ ψ : ℝ, 0 < ψ ∧ ∀ k, ∀ c ∈ cols R k, ψ * ‖stepOf P (R.Δ k) c‖ ≤ R.Δ k := by sorry

end LewisTorczon.BoundPS
