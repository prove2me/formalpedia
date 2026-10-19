-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_mode_maximum
-- name    : OAI.AsymptoticallyMinimalLittlewood.Sampling.mode_maximum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:00:25.176847+00:00
-- url     : https://prove2.me/theorems/74efef7a-90ca-4ca6-a13c-8073d40b1f83
-- title:
--   Uniform sup-norm bound for sampled chirp mode sums with sparse stationary points
-- statement:
--   Let $P$ be a finite index set and write $\mathbf e(x)=e^{2\pi\mathrm{i}x}$. For each $p\in P$ let $g_p:\mathbb{R}\to\mathbb{C}$ be smooth and compactly supported, with closed support contained in $(0,1)$ and with $|g_p(x)|\le1$ for all $x$, and let $c_p\in\mathbb{C}$ and $\lambda_p,b_p,d_p\in\mathbb{R}$ with $\lambda_p\neq0$. For a positive integer $N$ and $0\le k\le N-1$ put
--   $$
--   M_N(k)=\sum_{p\in P}c_p\,\mathbf e(Nd_p)\,g_p\Bigl(\frac kN\Bigr)\,\mathbf e\Bigl(\frac{\lambda_pk^2}{2N}+b_pk\Bigr).
--   $$
--   Assume:
--
--   1. (amplitude bound) $K\ge0$ and $|c_p|/\sqrt{|\lambda_p|}\le K$ for every $p\in P$;
--   2. (sparse stationary points) for every $t\in\mathbb{R}$, all $p,q\in P$ and all $l,m\in\mathbb{Z}$: if $g_p\bigl((l-(b_p+t))/\lambda_p\bigr)\neq0$ and $g_q\bigl((m-(b_q+t))/\lambda_q\bigr)\neq0$, then $p=q$ and $l=m$.
--
--   Then there is a constant $C\ge0$ such that for every integer $N\ge1$ and every $t\in[0,1]$,
--   $$
--   \Bigl|\frac{1}{\sqrt N}\sum_{k=0}^{N-1}M_N(k)\,\mathbf e(tk)\Bigr|\le K+\frac CN .
--   $$
--
--   The left-hand side is $N^{-1/2}|Q_N(z)|$ for the polynomial $Q_N(z)=\sum_{k=0}^{N-1}M_N(k)z^k$ at the point $z=\mathbf e(t)$ of the unit circle, so the theorem bounds the normalized maximum modulus of $Q_N$ on the unit circle by $K+O(1/N)$. Condition 2 says that for each $t$ at most one pair (mode $p$, dual frequency $l$) has its stationary point $(l-b_p-t)/\lambda_p$ where the amplitude $g_p$ is nonzero, so stationary contributions, each of modulus at most $|c_p|/\sqrt{|\lambda_p|}\le K$, never add up. In the construction of flat Littlewood polynomials this hypothesis is supplied by the signed interval packing.
--
--   **Formalization Note** `modeSum g c lam b d N k` is $M_N(k)$; the exponentials are `realPhase (2*Real.pi*N*d i)` $=\mathbf e(Nd_p)$, `phase (lam i/N) (-b i) k` $=\mathbf e(\lambda_pk^2/(2N)+b_pk)$ and `realPhase (2*Real.pi*t*k)` $=\mathbf e(tk)$, where `realPhase x` $=e^{\mathrm ix}$. The sum runs over `Fin N` and $1/\sqrt N$ is the complex number `1/(Real.sqrt N : ℂ)`. The constant $C$ depends on all the data but not on $N$ or $t$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/ModeSampling.lean#L173-L246

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Definitions.Def_OAI_Analysis_Littlewood_SamplingTail
import Definitions.Def_OAI_Analysis_Littlewood_SamplingEnergy
import Definitions.Def_OAI_Analysis_Littlewood_ModeSampling

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Sampling
universe uP
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Complex QuadraticTail

theorem OAI.AsymptoticallyMinimalLittlewood.Sampling.mode_maximum {P : Type uP} [Fintype P] (g : P → ℝ → ℂ) (c : P → ℂ)
    (lam b d : P → ℝ) (hgc : ∀ i, HasCompactSupport (g i))
    (hgs : ∀ i, ContDiff ℝ ∞ (g i)) (hgi : ∀ i, tsupport (g i)⊆Set.Ioo (0:ℝ) 1)
    (hgb : ∀ i x, ‖g i x‖≤1) (hlam : ∀ i, lam i≠0)
    {K : ℝ} (hK : 0≤K) (hc : ∀ i, ‖c i‖/Real.sqrt |lam i|≤K)
    (hsparse : ∀ t : ℝ, ∀ i j : P, ∀ l m : ℤ,
      g i (((l : ℝ)-(b i+t))/lam i)≠0 → g j (((m : ℝ)-(b j+t))/lam j)≠0 →
      i=j ∧ l=m) :
    ∃ C : ℝ, 0≤C ∧ ∀ N : ℕ, 1≤N → ∀ t∈Set.Icc (0:ℝ) 1,
      ‖(1/(Real.sqrt N : ℂ))*∑ k : Fin N,
        modeSum g c lam b d N k*realPhase (2*Real.pi*t*k)‖≤K+C/N := by sorry
