-- Prove2me | Theorems.Thm_NarrowDNF_Approx_lemma_3_1
-- name    : NarrowDNF.Approx.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:08:31.335832+00:00
-- url     : https://prove2.me/theorems/9c054b4b-1d44-4761-bfe2-66a2a9d3aac8
-- title:
--   Lemma 3.1 — One-coordinate shift
-- statement:
--   Let $0<p<1$, choose a coordinate $i$, let $f$ be increasing on the Boolean cube, and let $v$ be arbitrary. Choose $U_i$ with probability $1-p$ and $L_i$ with probability $p$, independently of the input. Then
--   $$(1-p)\mathbb P_p[f\ne U_iv]+p\mathbb P_p[f\ne L_iv]\le\mathbb P_p[f\ne v].$$
--   Both shifted functions are nondecreasing in coordinate $i$. For every other coordinate $j$ in which $v$ is already nondecreasing, both shifted functions remain nondecreasing in $j$.
--
--   This is the full expected-error and coordinate-monotonicity guarantee for a single shift.
--
--   Differences from the source:
--   - encoding: coordinates [n] and bits {0,1} → Fin n and Bool with pointwise false < true; reason: coordinate relabeling preserves all source instances
--   - encoding: product probabilities and expectations → published Bernoulli event sums and exact real finite weighted sums; reason: the finite product law is identical and every cost is integrable
--   - encoding: expectation over an independent two-point shift choice → the weighted sum (1-p) error(U_i v) + p error(L_i v); reason: this expands that expectation exactly, without sampling the input again
-- source:
--   Chenghua Liu, Boning Meng, STOC 2027 submission #1509 (October 2026), Lemma 3.1, p. 5 (PDF p. 6)

import Definitions.Def_NarrowDNF_Approx_Shifts

namespace NarrowDNF.Approx

theorem lemma_3_1 {n : ℕ} (p : ℝ) (i : Fin n) (f v : Cube n → Bool)
    (hp : 0 < p) (hp_one : p < 1) (hf : Monotone f) :
    (1 - p) * error p f (upper i v) + p * error p f (lower i v) ≤ error p f v ∧
    CoordinateMonotone (upper i v) i ∧ CoordinateMonotone (lower i v) i ∧
    (∀ j : Fin n, j ≠ i → CoordinateMonotone v j →
      CoordinateMonotone (upper i v) j ∧ CoordinateMonotone (lower i v) j) := by sorry

end NarrowDNF.Approx
