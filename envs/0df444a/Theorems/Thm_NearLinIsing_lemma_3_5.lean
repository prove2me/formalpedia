-- Prove2me | Theorems.Thm_NearLinIsing_lemma_3_5
-- name    : NearLinIsing.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:40:58.552392+00:00
-- url     : https://prove2.me/theorems/147c77e7-d09d-4c45-a0aa-f981c18433b5
-- title:
--   Lemma 3.5 — covariance below weighted radius $e$
-- statement:
--   Let a finite hard-core model with conflict matrix $A^\circ$ (no self-conflicts) have reference activities $w_i>0$, and let $u_i>0$ and $c<e$ satisfy $\sum_jA^\circ_{ij}w_ju_j\le cu_i$ for every $i$. After any feasible pinning, give the remaining coordinates activities $w_i'\le aw_i$, where $0<a\le1$, and write $p_i$ for their occupied marginals. On the nondeterministic coordinates,
--
--   $$\mathrm{Cov}(X)\preceq\mathrm{Diag}\Bigg(p_i\Bigg[1+\frac{a\sqrt{c\sum_jA^\circ_{ij}w_j}}{1-\sqrt{ac/e}}\Bigg]\Bigg).$$
--
--   This covariance bound feeds the upper-spectrum branch of Theorem 1.5.
--
--   Differences from the source:
--   - encoding: after any feasible pinning, the remaining coordinates → the hard-core law on an arbitrary coordinate set S with the conflict graph induced on it; reason: a pinning leaves an induced model, and every S arises by pinning the complement empty
--   - encoding: on the nondeterministic coordinates → the order is tested on vectors supported on S, with 0 < w′_i on S; reason: with positive activities the nondeterministic coordinates are exactly S
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, Lemma 3.5, p. 14

import Mathlib
import Definitions.Def_NearLinIsing_HardCore

namespace NearLinIsing

open Classical in
/-- **Lemma 3.5** (Covariance below weighted radius `e`), p. 14.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, Lemma 3.5, p. 14.

Let a finite hard-core model on `M` coordinates with conflict graph `A°` (no self-conflicts) have
reference activities `w_i > 0`, and let `u_i > 0` and `c < e` satisfy
`∑_j A°_{ij} w_j u_j ≤ c u_i` for every `i`. After any feasible pinning, give the remaining
coordinates `S` activities `0 < w'_i ≤ a w_i` with `0 < a ≤ 1`, and let `p_i` be their occupied
marginals. Then on the nondeterministic coordinates
`Cov(X) ⪯ Diag(p_i [1 + a √(c ∑_j A°_{ij} w_j) / (1 − √(ac/e))])`.

**Formalization Note.** A feasible pinning leaves the hard-core law on an induced set of
remaining coordinates; every subset `S` arises this way (pin its complement empty), so the
statement quantifies over all `S`. With positive activities the nondeterministic coordinates are
exactly those of `S`; the order `⪯` is tested on vectors supported on `S`. -/
theorem lemma_3_5 {M : ℕ} (Gc : SimpleGraph (Fin M)) (w u : Fin M → ℝ)
    (hw : ∀ i, 0 < w i) (hu : ∀ i, 0 < u i) (c : ℝ) (hc : c < Real.exp 1)
    (hwit : ∀ i, ∑ j, (if Gc.Adj i j then 1 else 0) * w j * u j ≤ c * u i)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1) (S : Finset (Fin M)) (w' : Fin M → ℝ)
    (hw' : ∀ i ∈ S, 0 < w' i ∧ w' i ≤ a * w i) :
    CovLeDiag (hcLaw Gc w' S)
      (fun i => mean (hcLaw Gc w' S) i *
        (1 + a * Real.sqrt (c * ∑ j, (if Gc.Adj i j then 1 else 0) * w j) /
          (1 - Real.sqrt (a * c / Real.exp 1)))) S := by sorry

end NearLinIsing
