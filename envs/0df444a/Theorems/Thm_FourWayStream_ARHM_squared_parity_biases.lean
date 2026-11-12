-- Prove2me | Theorems.Thm_FourWayStream_ARHM_squared_parity_biases
-- name    : FourWayStream.ARHM.squared_parity_biases
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:07.51782+00:00
-- url     : https://prove2.me/theorems/1c2506f1-6ba5-49bc-b123-4c4139a600e7
-- title:
--   Claim 5.10 — squared parity biases: $\sum_{u<v}\beta_{uv}^2\le4(1-\log_2E[f(X)])^2$
-- statement:
--   **Claim 5.10.** Let $f:\{0,1\}^N\to\{0,1\}$ be not identically zero, let $X$ be uniform on $\{0,1\}^N$, and for a pair $\{u,v\}$ let
--   $$\beta_{uv}=E\big[(-1)^{X_u+X_v}\,\big|\,f(X)=1\big].$$
--   Then
--   $$\sum_{u<v}\beta_{uv}^2\le4\big(1-\log_2E[f(X)]\big)^2.$$
--
--   Applied to the indicator of Alice's sending a given message, it bounds the advantage Bob can gain on the parities of pairs; it is a consequence of the Kahn–Kalai–Linial inequality.
--
--   Differences from the source:
--   - encoding: E[f(X)] and the conditional expectation given f(X) = 1 → |f⁻¹(1)|/2^N, and the average of (−1)^{x_u ⊕ x_v} over f⁻¹(1); reason: X uniform on a finite set; f ≢ 0 makes the conditioning well defined
--   - encoding: [N], [L], [m], [N − 1], edges {u, v}, bits in {0,1} → Fin N, Fin L, Fin m, Fin (N − 1) (0-based), Sym2 (Fin N), Bool with xor; reason: relabelling; no instance changes
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §5.2, p.23, Claim 5.10

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Stream

set_option autoImplicit false
open Classical

namespace FourWayStream.ARHM

/-- Claim 5.10, p.23. Let `f : {0,1}^N → {0,1}` be not identically zero and `X` uniform. For a pair
`{u, v}` let `β_uv = E[(−1)^{X_u + X_v} | f(X) = 1]`. Then
`Σ_{u<v} β_uv² ≤ 4 (1 − log₂ E[f(X)])²`. -/
theorem squared_parity_biases (N : ℕ) (f : (Fin N → Bool) → Bool) (hf : ∃ x, f x = true) :
    ∑ u : Fin N, ∑ v : Fin N,
        (if u < v then
          ((∑ x ∈ Finset.univ.filter (fun x => f x = true),
              (if xor (x u) (x v) then (-1 : ℝ) else 1)) /
            ((Finset.univ.filter (fun x => f x = true)).card : ℝ)) ^ 2
        else 0) ≤
      4 * (1 - Real.logb 2
        (((Finset.univ.filter (fun x => f x = true)).card : ℝ) / (2 : ℝ) ^ N)) ^ 2 := by sorry

end FourWayStream.ARHM
