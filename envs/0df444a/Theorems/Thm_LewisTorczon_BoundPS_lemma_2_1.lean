-- Prove2me | Theorems.Thm_LewisTorczon_BoundPS_lemma_2_1
-- name    : LewisTorczon.BoundPS.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:42:51.61084+00:00
-- url     : https://prove2.me/theorems/e8909ab0-cf87-4166-8dbd-7917af682385
-- title:
--   Lemma 2.1 — nonzero trial steps satisfy $\|s_k^i\|\ge\zeta_*\Delta_k$
-- statement:
--   Let $x_k,\Delta_k,C_k$ be a run of the generalized pattern search method for the bound constrained problem $\min\{f(x):\ell\le x\le u\}$ with basis matrix $B$. A trial step at iteration $k$ is $s_k^i=\Delta_k Bc_k^i$, where $c_k^i$ is a column of the generating matrix $C_k$.
--
--   Then there is a constant $\zeta_*>0$, independent of $k$, such that for every $k$ and every trial step $s_k^i\ne0$,
--   $$\|s_k^i\|\ge\zeta_*\,\Delta_k .$$
--
--   The lemma says that $\Delta_k$ bounds nonzero steps from below; it is used to show that $\{\Delta_k\}$ stays bounded when the iterates stay in a compact set, and to convert decrease proportional to $\|s_k^i\|$ into decrease proportional to $\Delta_k$.
--
--   **Formalization Note** The norm is Euclidean. The constant is allowed to depend on the run (in fact it depends only on $B$). The lemma is quoted in the paper from Torczon (1997), Lemma 3.1.
-- source:
--   Lewis & Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report No. 96-20 (NASA CR-198306), March 1996, p. 4, Lemma 2.1 (Lemma 3.1 from [14])

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_Box
import Definitions.Def_LewisTorczon_BoundPS_ProjQ
import Definitions.Def_LewisTorczon_BoundPS_GPS

namespace LewisTorczon.BoundPS

/-- **Lemma 2.1** (Lemma 3.1 of Torczon 1997), p. 4: there is `ζ_* > 0`, independent of `k`, with
`‖s_k^i‖ ≥ ζ_* Δ_k` for every nonzero trial step `s_k^i = Δ_k B c_k^i` of a generalized pattern
search run. -/
theorem lemma_2_1 {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m)
    (hR : IsGPSRun P lo hi f R) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ k, ∀ c ∈ cols R k,
      stepOf P (R.Δ k) c ≠ 0 → ζ * R.Δ k ≤ ‖stepOf P (R.Δ k) c‖ := by sorry

end LewisTorczon.BoundPS
