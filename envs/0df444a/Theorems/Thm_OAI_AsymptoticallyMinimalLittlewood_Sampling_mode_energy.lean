-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Sampling_mode_energy
-- name    : OAI.AsymptoticallyMinimalLittlewood.Sampling.mode_energy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:59:33.860429+00:00
-- url     : https://prove2.me/theorems/ce0d9ce3-53c3-4c08-a809-a7b9c995eccc
-- title:
--   Mean-square asymptotics of sampled chirp mode sums
-- statement:
--   Let $P$ be a finite index set and write $\mathbf e(x)=e^{2\pi\mathrm{i}x}$. For each $p\in P$ let $g_p:\mathbb{R}\to\mathbb{C}$ be smooth and compactly supported, with closed support contained in $(0,1)$ and with $|g_p(x)|\le1$ for all $x$, and let $c_p\in\mathbb{C}$ and $\lambda_p,b_p,d_p\in\mathbb{R}$. For a positive integer $N$ and $0\le k\le N-1$ define the mode sum
--   $$
--   M_N(k)=\sum_{p\in P}c_p\,\mathbf e(Nd_p)\,g_p\Bigl(\frac kN\Bigr)\,\mathbf e\Bigl(\frac{\lambda_pk^2}{2N}+b_pk\Bigr),
--   $$
--   a superposition of sampled chirps with amplitude $g_p$, curvature $\lambda_p/N$, linear frequency $b_p$ and constant phase $\mathbf e(Nd_p)$. Assume that for all $p\neq q$ in $P$ at least one of the following holds:
--
--   - $\lambda_p\neq\lambda_q$;
--   - $b_p-b_q\notin\mathbb{Z}$;
--   - $g_p(x)\,\overline{g_q(x)}=0$ for every $x\in\mathbb{R}$.
--
--   Then
--   $$
--   \lim_{N\to\infty}\frac1N\sum_{k=0}^{N-1}|M_N(k)|^2=\sum_{p\in P}|c_p|^2\int_{\mathbb{R}}|g_p(x)|^2\,dx .
--   $$
--
--   Under this frequency-separation condition the modes are asymptotically orthogonal in $\ell^2(\{0,\dots,N-1\})$, and the energy of each mode converges to $|c_p|^2\int|g_p|^2$, so the mean square of the superposition is asymptotically the sum of the individual energies. In the construction of flat Littlewood polynomials this computes the limiting mean square of the sampled sequence assembled from packed chirp blocks.
--
--   **Formalization Note** `modeSum g c lam b d N k` is $M_N(k)$, written with `realPhase (2*Real.pi*N*d i)` $=\mathbf e(Nd_p)$ (where `realPhase x` $=e^{\mathrm ix}$) and `phase (lam i/N) (-b i) k`, where `phase t u x` $=\exp(2\pi\mathrm i(tx^2/2-ux))$. The sum over $k$ runs over `Fin N`, the division is by the real number $N$ (Lean reads it as $0$ at $N=0$), and the limit is along $N\to\infty$ in $\mathbb{N}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/ModeSampling.lean#L73-L125

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

theorem OAI.AsymptoticallyMinimalLittlewood.Sampling.mode_energy {P : Type uP} [Fintype P] (g : P → ℝ → ℂ) (c : P → ℂ)
    (lam b d : P → ℝ) (hgc : ∀ i, HasCompactSupport (g i))
    (hgs : ∀ i, ContDiff ℝ ∞ (g i)) (hgi : ∀ i, tsupport (g i)⊆Set.Ioo (0:ℝ) 1)
    (hgb : ∀ i x, ‖g i x‖≤1)
    (hfreq : ∀ i j, i≠j → (lam i≠lam j ∨ ∀ l : ℤ, (l : ℝ)≠b i-b j) ∨
      ∀ x, g i x*conj (g j x)=0) :
    Tendsto (fun N : ℕ ↦ (∑ k : Fin N, ‖modeSum g c lam b d N k‖^2)/(N : ℝ))
      atTop (𝓝 (∑ i, ‖c i‖^2*(∫ x : ℝ, ‖g i x‖^2))) := by sorry
