-- Prove2me | Theorems.Thm_IntADSat_lemma_B_4
-- name    : IntADSat.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:51.728565+00:00
-- url     : https://prove2.me/theorems/4842d33f-5fb6-4bf3-88c8-51570a2660bd
-- title:
--   Lemma B.4 — relative variance of degree counts
-- statement:
--   Assume $n\ge2$ and let $G\sim G(n,1/2)$. For an integer $u$ let
--
--   $$
--   Z(u)=|\{v:\deg_G(v)\le u\}|,\qquad \pi=\Pr[\mathrm{Bin}(n-1,1/2)\le u],\qquad b=\Pr[\mathrm{Bin}(n-2,1/2)=u].
--   $$
--
--   Then, whenever $\pi>0$,
--
--   $$
--   \frac{\operatorname{Var}Z(u)}{(\mathbb EZ(u))^2}\le\frac1{n\pi}+\frac{b^2}{4\pi^2}.
--   $$
--
--   The analogous bound holds for the upper-tail count $Z'(u)=|\{v:\deg_G(v)\ge u\}|$ with $\pi'=\Pr[\mathrm{Bin}(n-1,1/2)\ge u]$ and the corresponding boundary point probability $b'=\Pr[\mathrm{Bin}(n-2,1/2)=u-1]$: whenever $\pi'>0$, $\operatorname{Var}Z'(u)/(\mathbb EZ'(u))^2\le 1/(n\pi')+b'^2/(4\pi'^2)$.
--
--   Combined with Chebyshev's inequality, this concentrates the number of vertices of low or high degree.
--
--   Differences from the source:
--   - reading: an analogous bound for upper-tail vertex counts, with the corresponding boundary point probability → Z'(u) = #{v : deg ≥ u}, π' = Pr[Bin(n−1,1/2) ≥ u], b' = Pr[Bin(n−2,1/2) = u − 1]; reason: in the proof deg(i) = A_ij + U_i and Pr[U ≥ u − 1] − Pr[U ≥ u] = Pr[U = u − 1]
--   - encoding: Var and 𝔼 under G(n, 1/2) → expect n (sum against the published product weight at 1/2); Var X = 𝔼[X²] − (𝔼X)²; reason: same quantities
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.4, p.16 (PDF 17)

import Mathlib
import Definitions.Def_QuasiPolyTrace_bin
import Definitions.Def_IntADSat_expect
import Definitions.Def_IntADSat_deg
import Definitions.Def_IntADSat_binomLE
import Definitions.Def_IntADSat_binomGE

set_option autoImplicit false

namespace IntADSat

/-- **Lemma B.4** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.16 (PDF 17)). Assume `n ≥ 2` and let `G ∼ G(n, 1/2)`. For an integer `u` let
`Z(u) = |{v : deg_G(v) ≤ u}|`, `π = Pr[Bin(n − 1, 1/2) ≤ u]`, `b = Pr[Bin(n − 2, 1/2) = u]`. Then
`Var Z(u) / (𝔼Z(u))² ≤ 1/(nπ) + b²/(4π²)` whenever `π > 0`. The analogous bound holds for the
upper-tail count `Z'(u) = |{v : deg_G(v) ≥ u}|` with `π' = Pr[Bin(n − 1, 1/2) ≥ u]` and the
boundary point probability `b' = Pr[Bin(n − 2, 1/2) = u − 1]`.

**Formalization Note** `Var X = 𝔼[X²] − (𝔼X)²` under `G(n, 1/2)`. The upper-tail boundary
probability is read off the proof: `deg(i) = A_ij + U_i` and `Pr[U ≥ u − 1] − Pr[U ≥ u] = Pr[U = u − 1]`. -/
theorem lemma_B_4 (n : ℕ) (hn : 2 ≤ n) (u : ℤ) :
    (0 < binomLE (n - 1) u →
      (expect n (fun G => ((Finset.univ.filter fun v => (deg G v : ℤ) ≤ u).card : ℝ) ^ 2) -
          expect n (fun G => ((Finset.univ.filter fun v => (deg G v : ℤ) ≤ u).card : ℝ)) ^ 2) /
        expect n (fun G => ((Finset.univ.filter fun v => (deg G v : ℤ) ≤ u).card : ℝ)) ^ 2 ≤
      1 / (n * binomLE (n - 1) u) + QuasiPolyTrace.bin (n - 2) u (1 / 2) ^ 2 / (4 * binomLE (n - 1) u ^ 2)) ∧
    (0 < binomGE (n - 1) u →
      (expect n (fun G => ((Finset.univ.filter fun v => u ≤ (deg G v : ℤ)).card : ℝ) ^ 2) -
          expect n (fun G => ((Finset.univ.filter fun v => u ≤ (deg G v : ℤ)).card : ℝ)) ^ 2) /
        expect n (fun G => ((Finset.univ.filter fun v => u ≤ (deg G v : ℤ)).card : ℝ)) ^ 2 ≤
      1 / (n * binomGE (n - 1) u) + QuasiPolyTrace.bin (n - 2) (u - 1) (1 / 2) ^ 2 / (4 * binomGE (n - 1) u ^ 2)) := by sorry

end IntADSat
