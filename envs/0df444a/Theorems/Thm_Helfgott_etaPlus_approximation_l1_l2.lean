-- Prove2me | Theorems.Thm_Helfgott_etaPlus_approximation_l1_l2
-- name    : Helfgott.etaPlus_approximation_l1_l2
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T00:32:26.781618+00:00
-- url     : https://prove2.me/theorems/3c68d223-ff74-470c-b965-461b5e8684e6
-- title:
--   Explicit L1 and L2 approximation for Helfgott's band-limited smoothing
-- statement:
--   Let $\eta_+$ and $\eta_\circ$ be the coordinated band-limited and compact smoothings in Helfgott's ternary Goldbach construction, with bandwidth $H=200$. Their difference and its square are integrable on the full real line, and
--
--   $$\int_{\mathbb R}|\eta_+(t)-\eta_\circ(t)|\,dt\le\frac1{1800},$$
--   $$\int_{\mathbb R}(\eta_+(t)-\eta_\circ(t))^2\,dt\le\frac1{6250000}.$$
--
--   Thus the $L^2$ distance is at most $1/2500=0.0004$. These explicit estimates control errors when replacing the compact smoothing by the actual Mellin-band-limited smoothing in the main convolution. They retain the full tails and allow the band-limited smoothing to be signed.
--
--   This is a coarser, independently derived approximation bound than the sharper numerical bound in the cited paper; it does not assert that the paper's sharper constant has been established. Its role is to provide proved quantitative input for subsequent major-arc estimates.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, §7, equations (7.4)–(7.5), and Major arcs for Goldbach's problem, https://arxiv.org/abs/1305.2897. The rational constants here are a coarser fourth-derivative Fourier-tail consequence for the same actual smoothing definitions, derived in the accompanying proof.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory

theorem Helfgott.etaPlus_approximation_l1_l2 :
    Integrable (fun t : ℝ => Helfgott.etaPlus t-Helfgott.etaCircle t) ∧
    Integrable (fun t : ℝ => (Helfgott.etaPlus t-Helfgott.etaCircle t)^2) ∧
    (∫ t : ℝ, |Helfgott.etaPlus t-Helfgott.etaCircle t|) ≤ 1/1800 ∧
    (∫ t : ℝ, (Helfgott.etaPlus t-Helfgott.etaCircle t)^2) ≤ 1/6250000 := by sorry
