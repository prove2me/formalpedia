-- Prove2me | Theorems.Thm_G26G_ref_block_alg
-- name    : G26G.ref_block_alg
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:30:44.345777+00:00
-- url     : https://prove2.me/theorems/e89ebc86-dcf3-4fe7-8847-f3c134f6d5bb
-- title:
--   Algebraic summation of the reference-block error terms
-- statement:
--   This is a purely deterministic inequality that collects the error terms of the reference block bound.
--
--   Let $d,u,n_C,m_0\in\mathbb N$ and $C,\varsigma,c_0,\tau_m,L\in\mathbb R$ with $\varsigma>0$, $c_0\ge0$, $1\le n_C\le u$, $0\le C\le n_C$, $u+1\le4(m_0+1)$, $(m_0+1)^{7/8}\le\tau_m$, $4\sqrt{n_C(u+1)}\le\tau_m$, $\tau_{2u}:=\mathrm{tauB}(\sqrt{n_C(u+1)},2u)\le(u+1)/4$, $L\ge1$,
--   $$
--   L^{512(d+1)}\le(4+c_0)^{512(d+1)}\,(512(d+1))!\cdot6\,(u+1),\qquad L\le(12+c_0)\frac{u+1}{n_C+1}.
--   $$
--   Let $P=4k$, $k=1024(d+1)$. Then the sum of the five error terms produced by the near-reference bound, the preparation bound (with $\rho=\tau_m(u+1)/(n_C+1)$), and the far-reference bound (with $\varepsilon=\varsigma/L^{1/8}$, $\rho=2(u+1)^2/(4\tau_{2u})$) is at most
--   $$
--   D(d,\varsigma,c_0)\Big(\Big(\frac{n_C+1}{u+1}\Big)^4+\frac1{(u+1)^4}\Big),
--   $$
--   where $D$ is the explicit constant `Dexpr d ς c₀`.
--
--   This is the bookkeeping that turns the probabilistic decomposition of Lemma G.29 into its polynomial form (G.622).
--
--   **Formalization Note** The exact left-hand side is displayed in the formal statement; `tauB z s` $=(s+1)^{7/8}+4z$ and `root8` is the eighth root.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, proof of Lemma G.29, the summation leading to (G.621) (pp.185–186)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run
import Definitions.Def_IAFTRL_G26_window

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11
open G26G
open G26 G26R
variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

theorem G26G.ref_block_alg {d u nC m0 : ℕ} {C sig c0 τm L : ℝ} (hsig : 0 < sig) (hc0 : 0 ≤ c0)
    (hnC1 : 1 ≤ nC) (hnu : nC ≤ u) (hC0 : 0 ≤ C) (hCn : C ≤ nC)
    (hu4 : (u : ℝ) + 1 ≤ 4 * ((m0 : ℝ) + 1))
    (hτm7 : root8 ((m0 : ℝ) + 1) ^ 7 ≤ τm) (hτmz : 4 * Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1)) ≤ τm)
    (hτ2 : tauB (Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) (2 * u) ≤ ((u : ℝ) + 1) / 4)
    (hL1 : 1 ≤ L)
    (hLq : L ^ (512 * (d + 1)) ≤
      ((4 + c0) ^ (512 * (d + 1)) * ((512 * (d + 1)).factorial : ℝ) * 6) * ((u : ℝ) + 1))
    (hL5 : L ≤ (12 + c0) * (((u : ℝ) + 1) / ((nC : ℝ) + 1))) :
    ∑ s ∈ Finset.Icc u (2 * u), cK d * ((s : ℝ) + 1) ^ (4 * kk d) /
          (((s : ℝ) + 2) ^ 4 / 2) ^ (4 * kk d) +
      (2 ^ (4 * kk d) * cK d * (((2 * u : ℕ) : ℝ) + 1) ^ (4 * kk d) /
          (τm * (((u : ℝ) + 1) / ((nC : ℝ) + 1))) ^ (4 * kk d) +
        2 ^ (4 * kk d) * 4 ^ d * ((τm * (((u : ℝ) + 1) / ((nC : ℝ) + 1))) / τm) ^ d /
          τm ^ (4 * kk d) *
          (Hneg (kk d) (16 * d + 1) (gB d) * (((2 * u : ℕ) : ℝ) + 1) ^ (3 * kk d) +
            ((((2 * u : ℕ) : ℝ) + 1) / ((nC : ℝ) + 1)) ^ (d + 2) *
              (2 ^ (4 * kk d) * (cK d * ((nC : ℝ) + 1) ^ (4 * kk d) + (2 * C) ^ (4 * kk d))))) +
      2 ^ (4 * kk d) * cK d * (((2 * u : ℕ) : ℝ) + 1) ^ (4 * kk d) /
        (2 * ((u : ℝ) + 1) ^ 2 / (4 * tauB (Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) (2 * u))) ^
          (4 * kk d) +
      (2 * (4 * tauB (Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) (2 * u))) ^ (4 * kk d) *
        ((2 * ((u : ℝ) + 1) ^ 2 / (4 * tauB (Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) (2 * u))) /
          (4 * tauB (Real.sqrt ((nC : ℝ) * ((u : ℝ) + 1))) (2 * u))) ^ d *
        (2 ^ (4 * kk d) * (4 / (((u : ℝ) + 1) * (sig / root8 L))) ^ (4 * kk d)) ≤
      Dexpr d sig c0 * ((((nC : ℝ) + 1) / ((u : ℝ) + 1)) ^ 4 + 1 / ((u : ℝ) + 1) ^ 4) := by sorry
