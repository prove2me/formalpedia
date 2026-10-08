-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_affineCube_plateau_site_approximation
-- name    : OAI.Erdos3.exists_affineCube_plateau_site_approximation
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-08T13:21:02.627625+00:00
-- url     : https://prove2.me/theorems/33e25706-adda-4d9c-9b7c-6b23ad6934b9
-- title:
--   Averaged affine-cube plateau approximations are sums of few Lipschitz site products
-- statement:
--   Section variables: finite types $B$ and $\alpha$ with decidable equality; a countable measurable type $T$ with measurable singletons; natural numbers $n,K,M$ with $M\ne0$; and, for $b\in B$ and $j\in\mathrm{Fin}(n+1)$, a `NormalizedScalarCubeSource α` $s_{b,j}$ (a structure bundling a length, moduli, residues and a normalized bounded Lipschitz weight, which determine a probability law `source` on an integer scalar cube box), $u_{b,j}\colon\mathrm{Option}\,\alpha\to\mathbb Z$ and $v_{b,j}\colon\mathrm{Option}\,\alpha\to\mathbb N$. Let $p$ be a probability mass function on $T$, assume $0<K$, let $H\in\mathbb R$, let $\mathrm{rows}$ be a finite set of finite subsets of $\alpha$, let $F$ be a finite set of frequencies $k\colon\mathrm{rows}\to\mathrm{Fin}\,M$, and let $D_k\ne0$, $a_k\colon\mathrm{rows}\to\mathbb Z$ and $\omega_k\colon\mathrm{rows}\to\mathbb R$ (for every frequency $k$) with $k_t/M=a_k(t)/D_k+\omega_k(t)/K$ for all $k\in F$ and $t\in\mathrm{rows}$. Let $\mathrm{shift}\colon T\to(\mathrm{rows}\to\mathbb Z)$, assume $(K/M)^{|\mathrm{rows}|}\le1$, and let $C$ be real with $\sum_k\big|\prod_{b}$ `affineWeightedCubeGridCoefficient (s b) (u b) (v b) M rows k`$\big|\le C$ (sum over all $k\colon\mathrm{rows}\to\mathrm{Fin}\,M$; the coefficient is the complex mean, under the product of the laws `(s b j).source`, of a unit-circle character of a Boolean block phase with frequencies $k_t/M$). Let $W\ge0$ with $|\omega_k(t)|\le W$ for $k\in F$, and reals $R,\delta,P$ with $R>0$, $\delta>0$, $P\ge0$, $R\le e^P$, $(\delta/(C+1))^{-1}\le e^P$ and $(2\pi\,|\mathrm{rows}|\,W+4)\,2^{|\alpha|}\le e^P$ (here $2\pi$ is `CircleFourier.characterLipConstant`). Then there is $N\colon F\to\mathbb N$ with $N_k\le e^{4P+8}$ for all $k$ and $|\texttt{PlateauSiteIndex}\ \alpha\ F\ N|\le|F|\,e^{2^{|\alpha|}(4P+8)}$, where `PlateauSiteIndex α F N` is the type of pairs of $k\in F$ and a map $\mathcal P(\alpha)\times\mathrm{Unit}\to\mathrm{Fin}\,N_k$; and there are $\beta\colon\texttt{PlateauSiteIndex}\to\mathbb C$ and functions $f_{\kappa,U,\varrho}\colon\mathbb R\to\mathbb C$ (for each index $\kappa$, $U\subseteq\alpha$ and $\varrho\in\mathbb Z/D_{\kappa}$, $D_\kappa$ meaning $D$ of the frequency component of $\kappa$) such that $\sum_\kappa|\beta_\kappa|\le C\,e^{2^{|\alpha|}(4P+8)+P}$, $|f_{\kappa,U,\varrho}|\le1$, each $f_{\kappa,U,\varrho}$ is $e^{1+6P+12}$-Lipschitz, and for every $y\colon\mathcal P(\alpha)\to\mathbb Z$ with $|y_U/K|\le R$ for all $U$,
--   $$\Big|\int\mathcal A(\mathrm{shift}(\zeta))\,dp(\zeta)-\sum_\kappa\beta_\kappa\prod_{U\subseteq\alpha}f_{\kappa,U,\,y_U\bmod D_\kappa}(y_U/K)\Big|\le\delta .$$
--   Here $\mathcal A(\sigma)=$ `affineCubePlateauApproximation s u v K H rows σ z F` with $z_t=$ `booleanCoefficient y t` $=\sum_{t'\subseteq t}(-1)^{|t\setminus t'|}y_{t'}$; that is, $\mathcal A(\sigma)$ is the product of `normalizedSupportPlateau H` (a $[0,1]$-valued cutoff of the sup norm) at $((z_t-\sigma_t)/K)_t$ with `integerGridApproximation` $(K/M)^{|\mathrm{rows}|}\sum_{k\in F}\hat p(k)\overline{\chi_k(z)}$ of the law of the shifted affine weighted-cube integer sum `affineWeightedCubeIntegerSum s u v rows σ` under `weightedCubeIntegerSource s`.
--
--   Lean: `OAI.Erdos3.exists_affineCube_plateau_site_approximation` in `lean/OAI/Combinatorics/Progressions/Lattices/AffineCubePlateauSite.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B088` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/AffineCubePlateauSite.lean#L58

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B088

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {B α T : Type*} [Fintype B] [DecidableEq B] [Fintype α] [DecidableEq α]
variable {n K M : ℕ} [NeZero M]
variable (s : B → Fin (n + 1) → NormalizedScalarCubeSource α)
variable (u : B → Fin (n + 1) → Option α → ℤ) (v : B → Fin (n + 1) → Option α → ℕ)

variable [Countable T] [MeasurableSpace T] [MeasurableSingletonClass T]

theorem exists_affineCube_plateau_site_approximation
    (p : PMF T) (hK : 0 < K) (H : ℝ) (rows : Finset (Finset α))
    (F : Finset (rows → Fin M)) (D : (rows → Fin M) → ℕ) [∀ k, NeZero (D k)]
    (a : (rows → Fin M) → rows → ℤ) (ω : (rows → Fin M) → rows → ℝ)
    (hfreq : ∀ k ∈ F, ∀ t, ((k t).val : ℝ) / M = (a k t : ℝ) / D k + ω k t / K)
    (shift : T → rows → ℤ) (hscale : ((K : ℝ) / M) ^ rows.card ≤ 1) {C : ℝ}
    (hcap : (∑ k, ‖∏ b, affineWeightedCubeGridCoefficient (s b) (fun j i => (u b j i : ℝ)) (v b) M rows k‖) ≤ C)
    (W : ℝ≥0) (hW : ∀ k ∈ F, ∀ t, |ω k t| ≤ W)
    {R δ P : ℝ} (hR : 0 < R) (hδ : 0 < δ) (hP : 0 ≤ P)
    (hRP : R ≤ Real.exp P) (hδP : (δ / (C + 1))⁻¹ ≤ Real.exp P)
    (hLP : ((CircleFourier.characterLipConstant * (rows.card * W) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp P) :
    ∃ N : F → ℕ, (∀ k, (N k : ℝ) ≤ Real.exp (4 * P + 8)) ∧
      (Fintype.card (PlateauSiteIndex α F N) : ℝ) ≤
        F.card * Real.exp (Fintype.card (Finset α) * (4 * P + 8)) ∧
      ∃ (β : PlateauSiteIndex α F N → ℂ)
        (f : (k : PlateauSiteIndex α F N) → Finset α → ZMod (D k.1) → ℝ → ℂ),
        (∑ k, ‖β k‖) ≤ C * Real.exp (Fintype.card (Finset α) * (4 * P + 8) + P) ∧
        (∀ k u r x, ‖f k u r x‖ ≤ 1) ∧
        (∀ k u r, LipschitzWith ⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ (f k u r)) ∧
        ∀ y : Finset α → ℤ, (∀ u, |(y u : ℝ) / K| ≤ R) →
          ‖(∫ zeta, affineCubePlateauApproximation s u v K H rows (shift zeta)
                (fun t => booleanCoefficient y t) F ∂p.toMeasure) -
            ∑ k, β k * ∏ u, f k u (y u : ZMod (D k.1)) ((y u : ℝ) / K)‖ ≤ δ := by
  sorry

end Erdos3
end
end OAI
