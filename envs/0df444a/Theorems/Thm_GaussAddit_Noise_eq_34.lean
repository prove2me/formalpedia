-- Prove2me | Theorems.Thm_GaussAddit_Noise_eq_34
-- name    : GaussAddit.Noise.eq_34
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:56.489358+00:00
-- url     : https://prove2.me/theorems/19a071f4-2ac5-482a-b8fa-a894edc65731
-- title:
--   Eq. (34), last identity — (1/n^k)/det[C + G†G/2] = 1/((n+1)^k − n^k) for the circulant matrices G, A of (27)–(28) and C of (26)
-- statement:
--   Let $n>0$ and $k\ge1$. Let $P$ be the $k\times k$ cyclic shift matrix, $P_{st}=1$ if $t=s+1$ (indices mod $k$) and $0$ otherwise, and put
--   $$G=P-\mathbb 1,\qquad A=P^{\mathsf T}-P,\qquad C=\frac{\mathbb 1}{n}+\frac A2 .$$
--   For $k\ge3$ these are the matrices (27), (28) and (26); for $k=2$, $A=0$, and for $k=1$, $G=A=0$, as the paper states. Then
--   $$\frac{1/n^k}{\det\!\big[C+G^{\dagger}G/2\big]}=\frac{1}{(n+1)^k-n^k}.$$
--
--   Raised to the $m$-th power this is the last identity of (34): it evaluates the eigenvalue $\lambda_0$ of $\Theta$ of maximum modulus as $[(n+1)^k-n^k]^{-m}$, which turns (22) into the bound (12). The first two identities of (34), which express $\lambda_0$ through the eigenvalues $d_j,e_j$ of (29), are not part of this item.
--
--   Differences from the source:
--   - encoding: {(1/n^k)/det[C + G†G/2]}^m = [1/((n + 1)^k − n^k)]^m → the identity of the bases, without the m-th power; reason: both bases are positive reals, so the two forms are equivalent
--   - encoding: G, A of (27)–(28) (printed for k ⩾ 3; A null for k = 2; G, A null for k = 1); G† → G = P − 1, A = Pᵀ − P with P the cyclic shift; Gᵀ; reason: entrywise equal to (27)–(28) for k ⩾ 3 and to the stated null cases for k ⩽ 2; G is real
--   - encoding: C = 11/n + A/2 of (26) and 1/n^k written with 1/n (defined only for n > 0) → hypothesis 0 < n; reason: excludes only n = 0, where the printed formula is undefined (P_n of (7) divides by n)
-- source:
--   Giovannetti & Lloyd, Additivity properties of a Gaussian channel, arXiv:quant-ph/0403075v3, p. 4, eq. (34) (last identity), with eqs. (26)–(28), p. 3

import Mathlib
import Definitions.Def_GaussAddit_Noise_Channel

open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace GaussAddit.Noise

theorem eq_34 (n : ℝ) (hn : 0 < n) (k : ℕ) (hk : 1 ≤ k) :
    let P : Matrix (Fin k) (Fin k) ℝ := fun s t => if t = finRotate k s then 1 else 0
    let G : Matrix (Fin k) (Fin k) ℝ := P - 1
    let A : Matrix (Fin k) (Fin k) ℝ := Pᵀ - P
    let C : Matrix (Fin k) (Fin k) ℝ := (1 / n) • (1 : Matrix (Fin k) (Fin k) ℝ) + (1 / 2 : ℝ) • A
    (1 / n ^ k) / (C + (1 / 2 : ℝ) • (Gᵀ * G)).det = 1 / ((n + 1) ^ k - n ^ k) := by sorry

end GaussAddit.Noise
