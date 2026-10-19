-- Prove2me | Theorems.Thm_OAI_Erdos3_affine_weightedModerateBlock_major_arc_s2
-- name    : OAI.Erdos3.affine_weightedModerateBlock_major_arc_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:04:45.98209+00:00
-- url     : https://prove2.me/theorems/fccf7660-c806-4274-a40a-71265e2fab09
-- title:
--   A large weighted moderate-block exponential sum with affine cube coordinates forces simultaneous rational approximation of the Boolean phase coefficients
-- statement:
--   All named objects below are defined by OpenAI. Let $n$ be a natural number and $I$ a finite type with decidable equality. Let $c$ be a `ScalarCubeLocalizationData Empty` and $d_0, \dots, d_{n-1}$ be `ScalarCubeLocalizationData I`. (A `ScalarCubeLocalizationData I` packages, among other things, a length $L$, a modulus function $\mathrm{modulus} : \texttt{Option}\ I \to \mathbb{N}_{>0}$ with residues, a weight function, and derived objects: a finite probability distribution `source` on `IntegerScalarCubeBox I L` (integer vectors indexed by `Option I` with entries in $[-L, L)$, reweighted residue-cube weights), a natural number `cellLength`, and an explicit error function `error` $: \mathbb{R} \to \mathbb{R}$.) Let $\tau_0, \dots, \tau_{n+1}$ be reals. Assume:
--   - $\tau_k > 0$ for $1 \le k \le n+1$;
--   - $c.\mathrm{error}(\tau_1) \le \tau_0$, and $d_j.\mathrm{error}(\tau_{j+2}) \le \tau_{j+1}$ for every $j < n$.
--
--   Let `shift` be a real number and $t$ a natural number with $t > 0$; let $u_j : \texttt{Option}\ I \to \mathbb{R}$ and $v_j : \texttt{Option}\ I \to \mathbb{N}$ for $j < n$ with all $v_j(i) > 0$; let $\xi$ be a real function on finite subsets of $I$, and $\mathcal{J}$ a finite set of subsets of $I$, each of cardinality at most $n$. Let $R$ be a real number with $v_j(i)\cdot d_j.\mathrm{modulus}(i) \le R$ for all $j, i$. Write $\beta$ = `multiaffineBiasBudget n τ_{n+1}` $= \texttt{denseProductDensityBudget}\ n\ \bigl(\tau_{n+1}^{2^n}/(2\cdot 3^n)\bigr)/\tau_{n+1}^{2^n}$. Assume:
--   - $\beta \le d_j.\mathrm{cellLength}$ for every $j$, and $\beta \le c.\mathrm{cellLength}$;
--   - (bias)
--   $$\tau_0 \le \Bigl|\mathbb{E}_{z \sim c.\mathrm{source}}\ \mathbb{E}_{x \sim \prod_j d_j.\mathrm{source}}\ e\Bigl(\bigl(\mathrm{shift} + t\, z_{\mathrm{none}}\bigr)\cdot \texttt{booleanBlockPhase}\ \xi\ \bigl(j \mapsto \texttt{affineCubeCoordinates}\ u_j\ v_j\ x_j\bigr)\Bigr)\Bigr|,$$
--   where $e(\theta) = e^{2\pi i\theta}$, $z_{\mathrm{none}}$ is the single coordinate of $z$, $x = (x_j)_{j<n}$ is drawn from the product distribution, `affineCubeCoordinates u v x` is the vector $i \mapsto u(i) + v(i)\,x(i)$, and `booleanBlockPhase ξ a` $= \sum_{S \subseteq I} \xi(S)\cdot$ `booleanCoefficient (booleanBlockValue a) S`, with `booleanBlockValue a T` $= \prod_{j<n} \bigl(a_j(\mathrm{none}) + \sum_{i \in T} a_j(\mathrm{some}\ i)\bigr)$ and `booleanCoefficient f S` $= \sum_{T \subseteq S} (-1)^{|S \setminus T|} f(T)$.
--
--   Then there are a natural number $D$ with
--   $$0 < D \le \Bigl(\beta \cdot \bigl(t\cdot c.\mathrm{modulus}(\mathrm{none})\bigr) R^n\Bigr)^{|\mathcal{J}|}$$
--   and integers $a_S$ ($S \in \mathcal{J}$) such that for every $S \in \mathcal{J}$,
--   $$\Bigl|\xi(S) - \frac{a_S}{D}\Bigr| \le \frac{\beta}{\bigl(t\cdot c.\mathrm{modulus}(\mathrm{none})\bigr)\cdot c.\mathrm{cellLength}\cdot \prod_{j<n} d_j.\mathrm{cellLength}}.$$
--
--   Lean: `OAI.Erdos3.affine_weightedModerateBlock_major_arc_s2`, which states OpenAI's `OAI.Erdos3.affine_weightedModerateBlock_major_arc` (in `lean/OAI/Combinatorics/Progressions/Fourier/PolynomialWeightedCubeMajorArc.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B108`, `OAIE3v2B125` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Fourier/PolynomialWeightedCubeMajorArc.lean (declaration OAI.Erdos3.affine_weightedModerateBlock_major_arc)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B108
import Definitions.Def_OAIE3v2B125

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem affine_weightedModerateBlock_major_arc_s2 {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : ScalarCubeLocalizationData Empty) (d : Fin n → ScalarCubeLocalizationData I)
    (τ : Fin (n + 2) → ℝ) (hτ : ∀ j : Fin (n + 1), 0 < τ j.succ)
    (hc : c.error (τ 1) ≤ τ 0)
    (hd : ∀ j : Fin n, (d j).error (τ j.succ.succ) ≤ τ j.castSucc.succ)
    (shift : ℝ) (t : ℕ) (ht : 0 < t) (u : Fin n → Option I → ℝ) (v : Fin n → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (ξ : Finset I → ℝ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    {R : ℝ} (hR : ∀ j i, ((v j i * (d j).modulus i : ℕ) : ℝ) ≤ R)
    (hN : ∀ j, multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ (d j).cellLength)
    (hM : multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ c.cellLength)
    (hbias : τ 0 ≤ ‖c.source.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean (fun x => character
        (((shift + (t : ℝ) * (z none : ℝ)) * booleanBlockPhase ξ
          (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle)))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ (multiaffineBiasBudget n (τ (Fin.last (n + 1))) *
        (((t * c.modulus none : ℕ) : ℝ) * R ^ n)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        multiaffineBiasBudget n (τ (Fin.last (n + 1))) /
          ((((t * c.modulus none : ℕ) : ℝ) * c.cellLength) * ∏ j, ((d j).cellLength : ℝ)) := by
  sorry

end Erdos3

end

end OAI
end
