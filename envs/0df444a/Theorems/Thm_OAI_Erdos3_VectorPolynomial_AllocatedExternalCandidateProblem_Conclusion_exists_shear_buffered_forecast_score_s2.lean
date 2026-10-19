-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedExternalCandidateProblem_Conclusion_exists_shear_buffered_forecast_score_s2
-- name    : OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.exists_shear_buffered_forecast_score_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T06:34:22.709992+00:00
-- url     : https://prove2.me/theorems/afc7ba4d-0a2c-4590-9356-acabb1d79891
-- title:
--   A conclusion of an allocated external candidate problem with a shear observable yields a retained path whose forecast target correlates with the buffered shear score
-- statement:
--   **Setting.** Fix $m \in \mathbb{N}$, finite types $G$ and $X$, families of types $I_j, E_j, J_j$ ($j \in \mathrm{Fin}\,m$; $I_j$ and $J_j$ finite), $n : \mathrm{Fin}\,m \to \mathbb{N}$, finite types $B_a$ indexed by the sampler axes `LayerSamplerAxis I n`, subspaces $U_j \subseteq \mathbb{R}^{J_j}$, bases $b_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of $U_j$ whose $\mathbb{Z}$-span is the projected integer lattice `projectedIntegerLattice` of $U_j$, orthonormal bases $o_j$ of $U_j$ indexed by $I_j$, reals $R_j > 0$, $\sigma_j > 0$, a `LayerSamplerScale` $S$, $N : X \to \mathbb{N}$, vector polynomials $\mathrm{poly}_j$ in the variables $X$ with values in $\mathbb{R}^{J_j}$ all of whose coefficients lie in $U_j$, reals $\tau, \xi$, $\mathrm{stride} : X \to \mathbb{N}$, a finite set `cells` of column residue patterns, and a point `center` of the coefficient torus, such that the section of the standard lattice $\mathbb{Z}^{J_j}$ by $U_j$ is a full lattice in $U_j$. Let $A$ be an `AllocatedExternalCandidateSampler` with these parameters: a proposition defined by OpenAI requiring $N_x > 0$ for all $x$, $\tau > 0$, $\xi > 0$, $\mathrm{stride}_x > 0$, nonemptiness of the trimmed integer box, and positivity of two explicit masses; it comes with a finite set of paths `A.Path`, a finite set of sites `A.Site` (the integer box with side lengths `A.sides`), a map `A.physical` from (path, site) to points of $\mathbb{Z}^X$, and a law `A.law` on paths. Write $K$ for the finite type `LayerSamplerVariables G I n B` of sampler variables and $|K|$ for its cardinality, and $\mathrm{Box}(N) = \{x \in \mathbb{Z}^X : 0 \le x_i < N_i\}$ (`integerBox N`).
--
--   Further fix types $Y$ and a Lie algebra $M$ over $\mathbb{Q}$, natural numbers $s, d, t$, a `PolynomialPatch Y s d` named `patch` (defined by OpenAI: weights in $[1, s]$, a polynomial slot form and a kernel), with finitely many shear indices; a nilpotent Lie filtration $F_{\mathrm{mark}}$ of $M$ of length $t$; a Lie algebra map $\varphi$ from the polynomial shear Lie algebra of `patch.weight` to $M$; a polynomial orbit `marked` in the realification of $F_{\mathrm{mark}}$; a function $f : \mathbb{Z}^X \to \mathbb{R}$ and a real $\lambda$; reals $\mathrm{cost}$, $\mathrm{massThreshold}$, $\mathrm{scoreThreshold}$, $\mathrm{outputCost}$, $\mathrm{outputMass}$, $\mathrm{outputScore}$; an `AllocatedExternalCandidateProblem` $P$ (a structure defined by OpenAI) for $A$, the polynomial shear nilmanifold of `patch`, $F_{\mathrm{mark}}$, $\varphi$, `marked`, the observable $(\_, z) \mapsto$ `patch.shearObservable z` and the weight $x \mapsto f(x) - \lambda$, with thresholds $\mathrm{cost}, \mathrm{massThreshold}, \mathrm{scoreThreshold}$; and `out`, a `P.Conclusion outputCost outputMass outputScore` (defined by OpenAI). Among its fields, `out` has an ambient polynomial orbit `out.ambient`, a finite set `out.retained` of paths contained in `P.productive`, and for each retained path $z$ a site law `out.siteLaw z` (a probability law on `A.Site`, uniform on the integer points of the slice of `out`).
--
--   **Hypotheses.** Let $u, p, p_{\mathrm{slice}}, p_{\mathrm{test}}, \mathrm{localBudget}, P_{\mathrm{native}}, \mathrm{forecastMassLog}, \mathrm{capLog}, E_{\mathrm{data}}, \mathrm{precision}, C$ be reals and write $Q = \max(\mathrm{localBudget}, 3P_{\mathrm{native}} + 3)$. Assume:
--   - $\xi \le 1$, and $2\,\texttt{spatialTrimMargin}\ \tau\ N\ x \le N_x$ for all $x \in X$, where `spatialTrimMargin τ N x` $= \lceil \tau N_x / 4 \rceil$;
--   - $0 \le u$, $0 \le p$, $0 \le \mathrm{localBudget}$, $0 \le P_{\mathrm{native}}$, $p_{\mathrm{slice}} \cdot |K| \le p$, $1 \le C \le e^{p}$, $\mathrm{capLog} \le p$;
--   - $2u + 4p + 12 \le E_{\mathrm{data}}$;
--   - $u + 2p + \max\bigl(Q,\ 2u + 4p + \max(0, \mathrm{forecastMassLog}) + 20\bigr) + 32 \le \mathrm{precision}$;
--   - `A.NativeDetection 0 pSlice pTest localBudget α` holds with $\alpha = $ `forecastAugmentedUnitThreshold u p (exp(pSlice·|K|)) C (exp capLog)`; `NativeDetection` is a property defined by OpenAI (a detection statement for niltests of degree $0$ on sites of $A$), and `forecastAugmentedUnitThreshold u p K C F` $= \bigl(e^{-(u+3)}/e^{2p}\bigr) / \max\bigl(1, (2KC + F)/e^{-(u+3)}\bigr)$;
--   - the excess mass of the site law `A.law.siteLaw (A.physicalBox …)` (the law on $\mathrm{Box}(N)$ of the physical point of a random path of `A.law` and a uniform site) over $C$ times the uniform law on $\mathrm{Box}(N)$, namely $\sum_{v} \max(q(v) - C/|\mathrm{Box}(N)|, 0)$ with $q$ that law, is at most $6\,e^{-(2\,\mathrm{precision} + 4)}$ (this is $6\cdot$`positiveProjectionAccuracy precision`);
--   - $0 \le p_{\mathrm{slice}}$, $\mathrm{outputCost} \le p_{\mathrm{slice}}$, $2 \le p_{\mathrm{test}}$;
--   - for every retained $z$ and every variable $i$ not kept by the chart `P.chart z`, `A.sides i` $\le e^{p_{\mathrm{slice}}}$;
--   - `Forecast` is a nonempty type and `data` assigns to each forecast an `ActualForecastData N poly Pnative forecastMassLog capLog Edata` (a structure defined by OpenAI: a target function $\mathrm{Box}(N) \to \mathbb{C}$ bounded by $e^{\mathrm{capLog}}$, approximated within an error controlled by $E_{\mathrm{data}}$ by a combination, of total coefficient mass at most $e^{\mathrm{forecastMassLog}}$, of normalized polynomial twists of the centered polynomials);
--   - $f(x) \in [0,1]$ for all $x \in \mathrm{Box}(N)$, and $\lambda \in [0,1]$;
--   - $\sigma_j \le 1$ for all $j$; $H : \mathrm{Fin}\,m \to \mathbb{R}$ with $H_j \ge 0$, $\|\Phi_j^{-1}(v)\| \le H_j \|v\|$ for all $v$, where $\Phi_j$ = `normalizedOrthogonalChart` of $U_j$ and $b_j$ (the linear chart $\mathbb{R}^{J_j} \cong U_j \times \mathbb{R}^{n_j}$ given by orthogonal projection and normalized $b_j$-coordinates), and $H_j \,(|I_j| + 1)\, R_j \le 1/8$;
--   - each $\mathrm{poly}_j$ has degree at most $j + 1$ (`DegreeLE 1 (j+1)`: every coefficient of a monomial of total degree $> j+1$ vanishes);
--   - $e : \mathrm{Fin}(\mathrm{tagCount}) \simeq \Sigma_j J_j$ is a bijection, and `select` maps each path of $A$ to a forecast;
--   - for each retained $z$, the target of `data (select z)` is real-valued (equal to its real part);
--   - $\mathrm{scoreLog}, \mathrm{massLogTransfer}, E_{\mathrm{compare}}$ are reals with $0 \le \mathrm{massLogTransfer}$, $e^{-\mathrm{scoreLog}} \le \mathrm{outputScore}$, $e^{-\mathrm{massLogTransfer}} \le \mathrm{outputMass}$, $\mathrm{scoreLog} + \mathrm{massLogTransfer} + 6 \le u$, and $\max\bigl(Q, 2u + 4p + \max(0, \mathrm{forecastMassLog}) + 20\bigr) + 2 + \mathrm{massLogTransfer} + \mathrm{scoreLog} + 8 \le E_{\mathrm{compare}}$;
--   - for every retained $z$ and every `NormalizedPolynomialTwist` $W$ on $X$ and $\Sigma_j J_j$ with period cap, cover cap and Lipschitz constant all equal to $e^{Q}$ (a structure defined by OpenAI: a modulus, a cover number, a mask of modulus at most $1$ and a smooth function of modulus at most $1$ with that Lipschitz constant), writing $W(x)$ for `W.eval N poly x`,
--   $$\Bigl| \mathbb{E}_{\mathrm{site} \sim \texttt{out.siteLaw}\ z}\, W(\texttt{A.physical}\ z\ \mathrm{site}) \;-\; \mathbb{E}_{x \in \mathrm{Box}(N)}\, W(x)\, \mathrm{target}_{z}(x) \Bigr| \le e^{-E_{\mathrm{compare}}},$$
--   where $\mathrm{target}_z$ is the target of `data (select z)`.
--
--   **Conclusion.** Let $\chi$ = `majorPhasePlateauKernel tagCount` (defined by OpenAI: the kernel $y \mapsto$ a linear cutoff of $\|y\|_\infty$ equal to $1$ for $\|y\| \le 1/8$ and $0$ for $\|y\| \ge 1/4$); let $\mathrm{coords}(x) \in \mathbb{R}^{\mathrm{tagCount}}$ = `fullTaggedBufferedCoordinates e poly (fun j => P.centerLift j)` $x$, whose $i$-th coordinate is the $(e\,i).2$-component of $\mathrm{poly}_{(e\,i).1}$ evaluated at $x$ minus the corresponding component of the center lift of $P$; let `returned` = `patch.ofTaggedWeightedShearOrbit e out.ambient` (a weighted parameter patch in the variables $X \sqcup \mathrm{Fin}(\mathrm{tagCount})$, defined by OpenAI); and for $v \in \mathrm{Box}(N)$ let
--   $$\mathrm{score}(v) = (f(v) - \lambda)\, \chi\bigl(\mathrm{coords}(v) - [\mathrm{coords}(v)]\bigr)\, \texttt{returned.value}\bigl(v, [\mathrm{coords}(v)]\bigr),$$
--   where $[y]$ is the coordinatewise nearest-integer lift of $y$ (this is `bufferedScalarScore`, defined by OpenAI). Then there is a retained path $z$ of `out` with
--   $$\frac{\mathrm{outputScore}}{2} \le \mathbb{E}_{x \in \mathrm{Box}(N)}\, \operatorname{Re}\bigl(\mathrm{target}_z(x)\bigr) \cdot \mathrm{score}(x).$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.exists_shear_buffered_forecast_score_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.exists_shear_buffered_forecast_score` (in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedExternalCandidateActualShearForecastScore.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B262`, `OAIE3v2B304`, `OAIE3v2B264` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedExternalCandidateActualShearForecastScore.lean (declaration OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.exists_shear_buffered_forecast_score)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B262
import Definitions.Def_OAIE3v2B304
import Definitions.Def_OAIE3v2B264

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem.Conclusion

variable {A} {Y M : Type} [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    (patch : PolynomialPatch Y s d) [Fintype (PolynomialShearIndex patch.weight)]
    {Fmark : NilpotentLieFiltration M t}
    {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    {cost massThreshold scoreThreshold outputCost outputMass outputScore : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le) Fmark φ marked
      (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
      cost massThreshold scoreThreshold}
    (out : P.Conclusion outputCost outputMass outputScore)

attribute [local instance] OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.instNonemptySite_4
theorem exists_shear_buffered_forecast_score_s2
    (hξone : ξ ≤ 1) (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x)
    {u p pSlice pTest localBudget Pnative forecastMassLog capLog Edata precision C : ℝ}
    (hu : 0 ≤ u) (hp : 0 ≤ p) (hbudget : 0 ≤ localBudget)
    (hNative : 0 ≤ Pnative)
    (hSliceLog : pSlice * Fintype.card (LayerSamplerVariables G I n B) ≤ p)
    (hC : 1 ≤ C) (hCp : C ≤ Real.exp p) (hCap : capLog ≤ p)
    (hAccuracy : 2 * u + 4 * p + 12 ≤ Edata)
    (hPrecision : u + 2 * p + max (max localBudget (3 * Pnative + 3))
      (2 * u + 4 * p + max 0 forecastMassLog + 20) + 32 ≤ precision)
    (hdirect : A.NativeDetection 0 pSlice pTest localBudget
      (forecastAugmentedUnitThreshold u p
        (Real.exp (pSlice * Fintype.card (LayerSamplerVariables G I n B))) C (Real.exp capLog)))
    (hexcess : (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).excessMass
      (A.law.siteLaw (A.physicalBox hξone hmargin)) C ≤ 6 * positiveProjectionAccuracy precision)
    (hSlice : 0 ≤ pSlice) (hcost : outputCost ≤ pSlice) (htest : 2 ≤ pTest)
    (hshort : ∀ z : out.retained, ∀ i : {i // ¬(P.chart ⟨z.val, out.subset z.property⟩).keep i},
      (A.sides i.val : ℝ) ≤ Real.exp pSlice)
    {Forecast : Type} [Nonempty Forecast]
    (data : Forecast → ActualForecastData N poly Pnative forecastMassLog capLog Edata)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    {tagCount : ℕ} (e : Fin tagCount ≃ Σ j, J j)
    (select : A.Path → Forecast)
    (hreal : ∀ z : out.retained, ∀ x,
      (((data (select z.val)).target x).re : ℂ) = (data (select z.val)).target x)
    {scoreLog massLogTransfer Ecompare : ℝ}
    (hTransferMass : 0 ≤ massLogTransfer)
    (hscoreLower : Real.exp (-scoreLog) ≤ outputScore)
    (hmassLower : Real.exp (-massLogTransfer) ≤ outputMass)
    (hU : scoreLog + massLogTransfer + 6 ≤ u)
    (hEcompare : max (max localBudget (3 * Pnative + 3))
        (2 * u + 4 * p + max 0 forecastMassLog + 20) + 2 +
      massLogTransfer + scoreLog + 8 ≤ Ecompare)
    (hcompare : ∀ z : out.retained,
      ∀ W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp (max localBudget (3 * Pnative + 3)))
        (Real.exp (max localBudget (3 * Pnative + 3)))
        ⟨Real.exp (max localBudget (3 * Pnative + 3)), Real.exp_nonneg _⟩,
      ‖(out.siteLaw z).complexMean
          (fun site => W.eval N poly (A.physical z.val site)) -
        (FiniteProbabilityWeights.uniformFinset (integerBox N) A.integerBox_nonempty).complexMean
          (fun x => W.eval N poly x.val * (data (select z.val)).target x)‖ ≤
        Real.exp (-Ecompare)) :
    let χ := majorPhasePlateauKernel tagCount
    let coords := fullTaggedBufferedCoordinates e poly (fun j => (P.centerLift j).val)
    let returned := patch.ofTaggedWeightedShearOrbit e out.ambient
    let score : integerBox N → ℝ := fun v =>
      bufferedScalarScore χ (fun x : integerBox N => coords x.val)
        (fun x lifts => returned.value
          (Sum.elim (fun i => (x.val i : ℝ)) (fun i => (lifts i : ℝ))))
        (fun x : integerBox N => f x.val) lam v
    ∃ z : out.retained, outputScore / 2 ≤
      𝔼 x : integerBox N, ((data (select z.val)).target x).re * score x := by
  sorry

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end
