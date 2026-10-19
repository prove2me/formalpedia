-- Prove2me | Theorems.Thm_OAI_Erdos3_box_smooth_pair_correlation_s2
-- name    : OAI.Erdos3.box_smooth_pair_correlation_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:11:23.469381+00:00
-- url     : https://prove2.me/theorems/ede20e09-dfef-4cdc-bf47-28ea10f33bd5
-- title:
--   Correlation bound for two box-supported functions sampled at a smooth random affine pair, via residue cell statistics
-- statement:
--   Let $J, I, A, B$ be finite types with decidable equality. Let $t, u : J \to \mathbb{Z}$ and $k \in J$ with $u(k) - t(k) \ne 0$. Let $H : I \to \mathbb{R}$ with $H(i) > 0$ for all $i$, reals $L, C, \kappa, \delta$ with $L \ge 1$, $C \ge 1$, $\kappa > 0$, $0 \le \delta \le 1$, and a natural number $Q$. Write $q$ = `affinePairModulus t u`, the absolute value of the gcd of the entries of $u - t$ (defined by OpenAI). Assume:
--   - $|t(j)/L| \le C$ and $|u(j)/L| \le C$ for all $j$; $\kappa \le |(u(k) - t(k))/L|$; $q \le Q$;
--   - $|u(k) - t(k)| \cdot L / H(i) \le \delta$ for all $i$;
--   - $4^{2 + \#\{j \in J : j \ne k\}} \cdot \texttt{smoothPairRowLipschitz}\ k \cdot \delta \le 1/2$, where `smoothPairRowLipschitz k` $= (\#\{j : j \ne k\} + 2) \cdot$ `probabilityProfileLipschitz` (OpenAI's Lipschitz constant of its smooth probability profile $\psi$).
--
--   Let $b : \operatorname{Option} J \times I \to \mathbb{Z}$, and let the scale of the coordinate $(c, i)$ be $\mathrm{sc}(c, i)$ = `smoothPairCoefficientScale (H i) L c`, i.e. $H(i)$ if $c = \mathrm{none}$ and $H(i)/L$ if $c = \mathrm{some}\ j$. Assume the mass $\sum_{z} \prod_{(c,i)} \psi\bigl((z(c,i) - b(c,i))/\mathrm{sc}(c,i)\bigr)$ over all $z : \operatorname{Option} J \times I \to \mathbb{Z}$ (`shiftedSmoothProductMass`) is positive, and let $\mathbb{P}$ = `smoothSourceFiniteWeights` be the corresponding normalized probability weights on $z$ (restricted to the finite set where the weight can be nonzero). For $z$ write $\mathrm{smp}_t(z)$ = `smoothAffineSample t z` $: i \mapsto z(\mathrm{none}, i) + \sum_j t(j)\, z(\mathrm{some}\ j, i)$, and similarly $\mathrm{smp}_u(z)$.
--
--   Let $\mathrm{lo}_T, \mathrm{hi}_T, \mathrm{lo}_U, \mathrm{hi}_U : I \to \mathbb{Z}$ with $\mathrm{lo}_T(i) < \mathrm{hi}_T(i)$, $\mathrm{lo}_U(i) < \mathrm{hi}_U(i)$, $q \le \mathrm{hi}_T(i) - \mathrm{lo}_T(i)$ and $q \le \mathrm{hi}_U(i) - \mathrm{lo}_U(i)$ for all $i$, and let $T, U$ be the (nonempty) integer boxes $\prod_i [\mathrm{lo}_T(i), \mathrm{hi}_T(i))$ and $\prod_i [\mathrm{lo}_U(i), \mathrm{hi}_U(i))$. Let $e, d : \mathbb{Z}^I \to \mathbb{R}$ vanish outside $T$ and $U$ respectively. Let $P : T \to A$ and $R : U \to B$ (cell labels), and $\mathrm{cell} : A \to B \to (I \to \mathbb{Z}/q) \to \mathbb{R}$. Let $\alpha, \beta, \mathrm{cap}, \zeta$ be reals with $\alpha \ge 0$, $\mathrm{cap} \ge 0$, $\zeta \ge 0$, and assume, writing $\rho(x) \in (\mathbb{Z}/q)^I$ for the coordinatewise residue of $x$ modulo $q$ (`integerVectorResidue`):
--   - for every label $a \in A$ and residue $r$: $\bigl|\mathbb{E}_{x \in T}\, [P(x) = a,\ \rho(x) = r]\, e(x)\bigr| \le \Pr_{x \in T}[P(x) = a] \cdot \alpha / q^{\#I}$ (with $x$ uniform on $T$; these are OpenAI's `finiteCellResidueMean` and `finiteCellWeights`);
--   - for every $b' \in B$ and $r$: $\bigl|\mathbb{E}_{y \in U}\, [R(y) = b',\ \rho(y) = r]\, d(y)\bigr| \le \Pr_{y \in U}[R(y) = b'] \cdot \beta / q^{\#I}$;
--   - $|\mathrm{cell}(a, b', r)| \le \mathrm{cap}$ for all $a, b', r$;
--   - for all $x \in T$, $y \in U$ with $\rho(x) = \rho(y)$: $\bigl| \texttt{shiftedPairLocationKernel t u k hne H L hH _ b}\ x\ y - \mathrm{cell}(P(x), R(y), \rho(x)) \bigr| \le \zeta$ (OpenAI's smooth pair product density evaluated at the normalized differences between the affine pair rows of the locations $(x, y)$ and the rows determined by $t, u, b$).
--
--   Then
--   $$\Bigl| \mathbb{E}_{z \sim \mathbb{P}}\, e(\mathrm{smp}_t(z))\, d(\mathrm{smp}_u(z)) \Bigr| \le \frac{\#T \cdot \#U}{\prod_i H(i)^2} \Bigl( \mathrm{cap}\, \alpha \beta + \bigl(\texttt{fullSmoothPairError}\ (\#I)\ k\ Q\ C\ \kappa\ \delta + \zeta\bigr) \cdot \frac{2^{\#I}}{2} \bigl( \mathbb{E}_{x \in T}\, e(x)^2 + \mathbb{E}_{y \in U}\, d(y)^2 \bigr) \Bigr),$$
--   where `fullSmoothPairError` is an explicit real function defined by OpenAI and the expectations over $T$ and $U$ are uniform.
--
--   Lean: `OAI.Erdos3.box_smooth_pair_correlation_s2`, which states OpenAI's `OAI.Erdos3.box_smooth_pair_correlation` (in `lean/OAI/Combinatorics/Progressions/Geometry/BoxPairCorrelation.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B126` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/BoxPairCorrelation.lean (declaration OAI.Erdos3.box_smooth_pair_correlation)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B126

section

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem box_smooth_pair_correlation_s2 {J I A B : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (t u : J → ℤ) (k : J) (hne : u k - t k ≠ 0)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : affinePairModulus t u ≤ Q)
    (hmesh : ∀ i, ((u k - t k).natAbs : ℝ) * L / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k * δ ≤ 1 / 2)
    (b : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (b z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (loT hiT loU hiU : I → ℤ)
    (hlenT : ∀ i, loT i < hiT i) (hlenU : ∀ i, loU i < hiU i)
    (hwidthT : ∀ i, (affinePairModulus t u : ℝ) ≤ ((hiT i - loT i : ℤ) : ℝ))
    (hwidthU : ∀ i, (affinePairModulus t u : ℝ) ≤ ((hiU i - loU i : ℤ) : ℝ))
    (T U : Finset (I → ℤ)) [Nonempty T] [Nonempty U]
    (hT : T = Fintype.piFinset (fun i => Finset.Ico (loT i) (hiT i)))
    (hU : U = Fintype.piFinset (fun i => Finset.Ico (loU i) (hiU i)))
    (e d : (I → ℤ) → ℝ) (heoff : ∀ x ∉ T, e x = 0) (hdoff : ∀ y ∉ U, d y = 0)
    (P : T → A) (R : U → B) (cell : A → B → (I → ZMod (affinePairModulus t u)) → ℝ)
    {alpha beta cap zeta : ℝ} (halpha : 0 ≤ alpha) (hcap : 0 ≤ cap) (hzeta : 0 ≤ zeta)
    (he : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform T) P
      (fun x => integerVectorResidue (affinePairModulus t u) x.val) (fun x => e x.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform T) P).weight c * alpha /
        (affinePairModulus t u : ℝ) ^ Fintype.card I)
    (hd : ∀ c r, |finiteCellResidueMean (FiniteProbabilityWeights.uniform U) R
      (fun y => integerVectorResidue (affinePairModulus t u) y.val) (fun y => d y.val) c r| ≤
      (finiteCellWeights (FiniteProbabilityWeights.uniform U) R).weight c * beta /
        (affinePairModulus t u : ℝ) ^ Fintype.card I)
    (hcell : ∀ c c' r, |cell c c' r| ≤ cap)
    (hgrid : ∀ x : T, ∀ y : U,
      integerVectorResidue (affinePairModulus t u) x.val = integerVectorResidue (affinePairModulus t u) y.val →
      |shiftedPairLocationKernel t u k hne H L hH (zero_lt_one.trans_le hL) b x.val y.val -
        cell (P x) (R y) (integerVectorResidue (affinePairModulus t u) x.val)| ≤ zeta) :
    |(smoothSourceFiniteWeights (fun z => (b z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
      (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).mean
      (fun z => e (smoothAffineSample t z.val) * d (smoothAffineSample u z.val))| ≤
      ((T.card : ℝ) * U.card / ∏ i, H i ^ 2) *
        (cap * alpha * beta + (fullSmoothPairError (Fintype.card I) k Q C κ δ + zeta) * ((2 : ℝ) ^ Fintype.card I / 2 *
          ((FiniteProbabilityWeights.uniform T).mean (fun x => e x.val ^ 2) +
           (FiniteProbabilityWeights.uniform U).mean (fun y => d y.val ^ 2)))) := by
  sorry

end Erdos3

end

end OAI
end
