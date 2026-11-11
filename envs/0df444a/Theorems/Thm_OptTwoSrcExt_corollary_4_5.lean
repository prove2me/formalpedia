-- Prove2me | Theorems.Thm_OptTwoSrcExt_corollary_4_5
-- name    : OptTwoSrcExt.corollary_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:08.575192+00:00
-- url     : https://prove2.me/theorems/a1baf925-9971-42e4-9cee-e774644c9244
-- title:
--   Corollary 4.5 — common error calibration of the one-payload bound
-- statement:
--   Write the one-payload error of Lemma 4.1 as $\beta+\tfrac12\sqrt{\theta+2\beta+2(1+\theta)D^2\gamma+DM/K}$ with $\beta=3(1+\theta)\zeta/\theta+2\eta$, $D=2^d$, $M=2^p$, $K=2^k$. Let $0<\varepsilon\le1/4$ and
--   $$\theta=\frac{\varepsilon^2}{64},\quad\zeta\le\frac{\varepsilon^4}{2^{20}},\quad\eta\le\frac{\varepsilon^2}{4096},\quad\gamma\le\frac{\varepsilon^2}{512D^2},\quad\frac{DM}{K}\le\frac{\varepsilon^2}{64}.$$
--   Then:
--   1. the one-payload error is at most $\varepsilon/4$;
--   2. if also $\zeta_R\le\varepsilon^4/2^{20}$, the concatenated-output error (the one-payload error plus $\zeta_R$, Corollary 4.4) is less than $\varepsilon$;
--   3. $K\ge16M$.
--
--   This fixes the parameters of the construction of Theorem 1.5 so that its output error is at most $\varepsilon$.
--
--   **Formalization Note** A statement about real numbers; $d,p$ are natural numbers and $k$ is real. The errors $\zeta,\eta,\gamma,\zeta_R$ carry no sign hypothesis.
--
--   Differences from the source:
--   - generalization: errors ζ, η, γ, ζR (nonnegative, as errors) → arbitrary real numbers bounded above as stated; reason: the bound is monotone in each; the paper's nonnegative errors are a special case
--   - reading: the one-payload error; the concatenated output has error → the right side of (4.1); that quantity plus ζR; reason: the quantities Lemma 4.1 and Corollary 4.4 bound
--   - encoding: D, M, K → 2^d, 2^p, 2^k with d, p natural and k real; reason: as defined in Lemma 4.1
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Corollary 4.5, p.85 (PDF p.87)

import Mathlib

namespace OptTwoSrcExt

/-- **Corollary 4.5 (Common error calibration).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Corollary 4.5, printed p.85 (PDF p.87): "For 0 < ε ⩽ 1/4,
the one-payload error is at most ε/4 if θ = ε²/64, ζ ⩽ ε⁴/2²⁰, η ⩽ ε²/4096, γ ⩽ ε²/(512D²),
DM/K ⩽ ε²/64. If also ζR ⩽ ε⁴/2²⁰, the concatenated output has error less than ε. The bound on DM/K
implies K ⩾ 16M."

The one-payload error is the right side of (4.1),
`β + ½ √(θ + 2β + 2(1 + θ)D²γ + DM/K)` with `β = 3(1 + θ)ζ/θ + 2η`, `D = 2^d`, `M = 2^p`, `K = 2^k`;
the concatenated output error is that plus `ζ_R` (Corollary 4.4). For `0 < ε ≤ 1/4`, `θ = ε²/64`,
`ζ ≤ ε⁴/2²⁰`, `η ≤ ε²/4096`, `γ ≤ ε²/(512D²)` and `DM/K ≤ ε²/64`:
1. the one-payload error is at most `ε/4`;
2. if also `ζ_R ≤ ε⁴/2²⁰`, the one-payload error plus `ζ_R` is less than `ε`;
3. `K ≥ 16M`.

**Formalization Note.** A statement about real numbers; `d, p` are natural numbers and `k` is real, as in
Lemma 4.1. The errors `ζ, η, γ, ζ_R` are arbitrary reals bounded above (no sign hypothesis is needed). -/
theorem corollary_4_5 (ε ζ η γ ζR k : ℝ) (d p : ℕ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 4)
    (hζ : ζ ≤ ε ^ 4 / 2 ^ 20) (hη : η ≤ ε ^ 2 / 4096)
    (hγ : γ ≤ ε ^ 2 / (512 * ((2 : ℝ) ^ d) ^ 2))
    (hDMK : (2 : ℝ) ^ d * (2 : ℝ) ^ p / (2 : ℝ) ^ k ≤ ε ^ 2 / 64) :
    (3 * (1 + ε ^ 2 / 64) * ζ / (ε ^ 2 / 64) + 2 * η) +
        1 / 2 * Real.sqrt (ε ^ 2 / 64 + 2 * (3 * (1 + ε ^ 2 / 64) * ζ / (ε ^ 2 / 64) + 2 * η) +
          2 * (1 + ε ^ 2 / 64) * ((2 : ℝ) ^ d) ^ 2 * γ + (2 : ℝ) ^ d * (2 : ℝ) ^ p / (2 : ℝ) ^ k) ≤
      ε / 4 ∧
    (ζR ≤ ε ^ 4 / 2 ^ 20 →
      (3 * (1 + ε ^ 2 / 64) * ζ / (ε ^ 2 / 64) + 2 * η) +
          1 / 2 * Real.sqrt (ε ^ 2 / 64 + 2 * (3 * (1 + ε ^ 2 / 64) * ζ / (ε ^ 2 / 64) + 2 * η) +
            2 * (1 + ε ^ 2 / 64) * ((2 : ℝ) ^ d) ^ 2 * γ + (2 : ℝ) ^ d * (2 : ℝ) ^ p / (2 : ℝ) ^ k) +
          ζR < ε) ∧
    16 * (2 : ℝ) ^ p ≤ (2 : ℝ) ^ k := by sorry

end OptTwoSrcExt
