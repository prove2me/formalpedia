-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_forecastInactive_sliced_retained_character_sites_s2
-- name    : OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_retained_character_sites_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:30:23.540795+00:00
-- url     : https://prove2.me/theorems/09c6152a-e6d3-4f9e-a4ad-19c7fa9b8b3b
-- title:
--   Low-order character sums of the inactive forecast output are approximated by mixtures of bounded scalar site expansions
-- statement:
--   All named objects below are defined by OpenAI. Let $m$ be a natural number, $G$ a finite type, and for $j < m$ let $I_j$ (with decidable equality), $J_j$ be finite types and $n_j$ natural numbers; let $B_a$ be finite types with decidable equality indexed by `LayerSamplerAxis I n`. For each $j$ let $U_j$ be a real subspace of $\mathbb{R}^{J_j}$ and `basis j` a basis, indexed by $\{0,\dots,n_j-1\}$, of the orthogonal complement of the Euclidean copy of $U_j$. Let $R_j, \sigma_j$ be reals with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U basis R σ` (scale value `S.value`). Write $\mathcal{T}$ for `PrincipalTupleIndex B (layerSamplerDegree I n)` and sides for `allocatedPrincipalSides B U basis S`. Let $H, \mathrm{step} : \mathcal{T} \to \mathbb{N}$ and $c : \mathcal{T} \to \mathbb{Z}$ with $H(t) > 0$ for all $t$ (proof `hH`), and (`hsubset`) for every $t$ the progression $\{c(t) + \mathrm{step}(t)\,k : 0 \le k < H(t)\}$ contained in $[0, \mathrm{sides}(t))$. Let $A$, $V_{\mathrm{act}}$, Out be finite types (the last two with decidable equality).
--
--   Let `selected` be an injective map from $A$ to pairs $(j, i)$ with $i < n_j$; for $a \in A$ write $(j_a, i_a)$ = `selected a`, $\bar a$ for the axis $(j_a, \mathrm{inr}\ i_a)$ and $h_a$ = `basisAxisScale (basis j_a) i_a`. Let `poly o` ($o \in$ Out) be integer polynomials in the variables $V_{\mathrm{act}} \sqcup (\mathcal{T} \times \texttt{Option Empty})$; $N$ a nonzero natural number; $p_{\mathrm{Rat}}$ a finite probability distribution on $(\mathbb{Z}/N)^{V_{\mathrm{act}}}$; $T$ a natural number with $T > 0$; $\delta, P$ reals and `Hchild` a natural number. Assume:
--   - $\delta > 0$;
--   - for every $a$: either some $\beta, v$ have $\mathrm{sides}(\bar a, \beta, v) < $ `Hchild`, or for all $\beta, v$ both $\delta\,\mathrm{sides}(\bar a, \beta, v) \le H(\bar a, \beta, v)$ and $0 < \mathrm{step}(\bar a, \beta, v)$;
--   - for every $a$: $h_a \le \mathrm{S.value}^{j_a+1}$, and $\bar a$ is a grid axis (`allocatedGridAxis U basis S.value`);
--   - `coefficients a` is an integer vector indexed by `BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j_a+1)` whose entry at each $d$ lies in the support of `allocatedLayerIntegerPMFs B U basis hR hσ S j_a i_a d`;
--   - $\sigma_{j_a} \le 1$ for all $a$;
--   - $L$ is a nonnegative real such that `Real.smoothTransition` is $L$-Lipschitz; $1 \le P$; `scalarCubePrimitiveEnvelope Empty L 1 0 T` $\le P$; $\mathrm{step}(\bar a, \beta, v)\cdot T \le P$ for all $a, \beta, v$;
--   - `uniformSpectrumBlockCount j_a 1 (j_a+1)` $\le |B_{\bar a}|$ for all $a$;
--   - $C_{\mathrm{actual}}, \delta_{\mathrm{out}}, Q, N_t, V_t, C_t, H_t$ are reals and $L_t$ a nonnegative real with $0 \le C_{\mathrm{actual}}$, $0 \le C_t$, $0 < \delta_{\mathrm{out}}$, $0 \le Q$, and for every natural number $q$ with $0 < q \le T$, `forecastInactiveSlicedSiteNumerics B selected q Hchild δ P Cactual δout Q Nt Vt Ct Ht Lt` holds (an explicit list of numerical inequalities defined by OpenAI).
--
--   Define: $p$ = `principalTupleWeights B (layerSamplerDegree I n) H hH` (product of integer scalar cube weights with sides $H$, index type $\alpha$ empty); map = `containedProgressionTupleMap` (sending a tuple $y$ with entries in $[0, H)$ to the tuple with entries $c + \mathrm{step}\cdot y$ in $[0, \mathrm{sides})$); law $= p$ pushed forward by map (`fiberLaw`); Ch the set of additive characters $\chi$ of $(\mathbb{Z}/N)^{\mathrm{Out}}$ with $\operatorname{ord}\chi \le T$; for $\chi \in$ Ch, $\mathrm{Pos}(\chi)$ the set of residue patterns $r : \mathcal{T} \times \texttt{Option Empty} \to \mathbb{Z}/\operatorname{ord}\chi$ whose residue cell has positive $p$-mass; and
--   $$\mathrm{weight}(\chi, r) = p\bigl(\{y : y \bmod \operatorname{ord}\chi = r\}\bigr)\cdot \texttt{forecastInactiveCharacterCoefficient poly N pRat}\ \chi\ \bigl(\texttt{progressionPrincipalResidue B (layerSamplerDegree I n) step c (ord χ)}\ r\bigr),$$
--   where `progressionPrincipalResidue … r` $= c\cdot[\text{constant slot}] + \mathrm{step}\cdot r$ and `forecastInactiveCharacterCoefficient` is the $p_{\mathrm{Rat}}$-average of $\chi$ applied to the output vector $(\texttt{poly}\ o)$ evaluated at the active variables and the inactive residues (reduced mod $N$).
--
--   Then there exist scalar site expansions $e(\chi, r, a)$ (each a `ScalarSiteExpansion` on the one-element site type `Finset Empty`: a finite family of terms with periods, complex coefficients and complex factor functions) such that:
--   - every $e(\chi, r, a)$ satisfies `Bounds Nt Vt Ct Lt Ht`: at most $N_t$ terms, positive periods at most $V_t$, coefficient $\ell^1$-norm at most $C_t$, factors of norm at most $1$, $L_t$-Lipschitz in the real argument, and vanishing when the real argument has absolute value at least $H_t$;
--   - $\sum_{\chi \in \mathrm{Ch}} \sum_{t} \bigl|\texttt{forecastSiteMixtureCoefficient}\ (e\ \chi)\ (\mathrm{weight}\ \chi)\ t\bigr| \le T^{|\mathrm{Out}|+1} C_t^{|A|}$, where $t$ runs over pairs of $r \in \mathrm{Pos}(\chi)$ and a choice of term of $e(\chi, r, a)$ for every $a$, and the mixture coefficient is $\mathrm{weight}(\chi, r)\prod_a$ (coefficient of the chosen term);
--   - for every $x : G \to$ `IntegerScalarCubeBox Empty S.value`, every $z : A \to \mathbb{Z}$ and every `outPoint` $\in (\mathbb{Z}/N)^{\mathrm{Out}}$,
--   $$\Bigl|\sum_{\chi \in \mathrm{Ch}} \Bigl(\prod_a h_a\Bigr) \mathbb{E}_{y \sim \mathrm{law}}\Bigl[\Psi_\chi(y)\cdot \mathbf{1}\bigl[\texttt{forecastInactiveFixedOutput B U basis S selected coefficients x y} = (a, \_ \mapsto z_a)\bigr]\Bigr]\overline{\chi(\mathrm{outPoint})} - \sum_{\chi \in \mathrm{Ch}} \Bigl(\sum_{r \in \mathrm{Pos}(\chi)} \mathrm{weight}(\chi, r)\, \texttt{siteFamilyEval}\ (e\ \chi\ r)\ (\_ \mapsto z)\ (\_\ a \mapsto z_a/h_a)\Bigr)\overline{\chi(\mathrm{outPoint})}\Bigr| \le T^{|\mathrm{Out}|+1}\,\delta_{\mathrm{out}},$$
--   where $\Psi_\chi(y)$ = `finiteImageCharacteristic pRat` $(t \mapsto (\texttt{integerLongPolynomialOutput poly}\ y\ N\ t \bmod N))\ \chi$ is the $p_{\mathrm{Rat}}$-average over $t$ of $\chi$ of the vector of values of the `poly o` at $(t, y)$, reduced mod $N$; `forecastInactiveFixedOutput … x y` is, for each $a$, the product of OpenAI's bounded coefficient jet matrix (built from the physical cube root and directions of $x, y$) with `coefficients a`; and `siteFamilyEval` is the product over $a$ of the evaluations of the expansions $e(\chi, r, a)$ at integer value $z_a$ and real value $z_a/h_a$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_retained_character_sites_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_retained_character_sites` (in `lean/OAI/Combinatorics/Progressions/Sampling/ForecastInactiveSlicedCappedContinuousSource.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B180`, `OAIE3v2B197` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/ForecastInactiveSlicedCappedContinuousSource.lean (declaration OAI.Erdos3.VectorPolynomial.exists_forecastInactive_sliced_retained_character_sites)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B197

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable {A : Type*} [Fintype A]
attribute [local instance] ScalarSiteExpansion.termFinite

variable {Vact Out : Type*} [Fintype Vact] [DecidableEq Vact] [Fintype Out] [DecidableEq Out]

attribute [local instance] OAI.Erdos3.VectorPolynomial.instNeZeroNatOrderOfAddCharForallZModComplex_1
theorem exists_forecastInactive_sliced_retained_character_sites_s2
    (selected : A → Σ j : Fin m, Fin (n j))
    (hselected : Function.Injective selected)
    (poly : Out → MvPolynomial (Vact ⊕ (PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty)) ℤ)
    (N : ℕ) [NeZero N] (pRat : FiniteProbabilityWeights (Vact → ZMod N))
    (T : ℕ) (_hT : 0 < T)
    (δ P : ℝ) (Hchild : ℕ) (hδ : 0 < δ)
    (hreg : ∀ a, (∃ b0 v0,
      allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b0,v0⟩ < Hchild) ∨
      ((∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ ≤
        (H ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ : ℝ)) ∧
       (∀ b v, 0 < step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩)))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hgrid : ∀ a, allocatedGridAxis (I := I) U basis S.value ⟨(selected a).1, Sum.inr (selected a).2⟩)
    (coefficients : ∀ a, BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1) → ℤ)
    (hcoefficients : ∀ a d, coefficients a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S
      (selected a).1 (selected a).2 d).support)
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hP : 1 ≤ P) (hsP : scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ P)
    (hstride : ∀ a b v, ((step ⟨⟨(selected a).1,Sum.inr (selected a).2⟩,b,v⟩ * T : ℕ) : ℝ) ≤ P)
    (hB : ∀ a, uniformSpectrumBlockCount (selected a).1.val 1 ((selected a).1.val + 1) ≤
      Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩))
    (Cactual δout Q Nt Vt Ct Ht : ℝ) (Lt : ℝ≥0)
    (hCactual : 0 ≤ Cactual) (hCtNonneg : 0 ≤ Ct) (hδout : 0 < δout) (hQ : 0 ≤ Q)
    (hnumerics : ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild
        δ P Cactual δout Q Nt Vt Ct Ht Lt) :
    let p := principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH
    let map := containedProgressionTupleMap B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hsubset
    let law := p.fiberLaw map
    let Ch := Finset.univ.filter (fun χ : AddChar (Out → ZMod N) ℂ => orderOf χ ≤ T)
    let Pos := fun χ : Ch =>
      {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod (orderOf χ.val) //
        0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r))}
    let height := fun a => basisAxisScale (basis (selected a).1) (selected a).2
    let weight := fun (χ : Ch) (r : Pos χ) =>
      (p.mass (Finset.univ.filter (fun y => principalResidueLabel (orderOf χ.val) y = r.val)) : ℂ) *
        forecastInactiveCharacterCoefficient poly N pRat χ.val
          (progressionPrincipalResidue B (layerSamplerDegree I n) step c (orderOf χ.val) r.val)
    ∃ e : ∀ χ : Ch, Pos χ → A → ScalarSiteExpansion.{0,0} (Finset Empty),
      (∀ χ r a, (e χ r a).Bounds Nt Vt Ct Lt Ht) ∧
      (∑ χ : Ch, ∑ t : Σ r : Pos χ, ∀ a, (e χ r a).Term,
        ‖forecastSiteMixtureCoefficient (e χ) (weight χ) t‖) ≤
        (T : ℝ) ^ (Fintype.card Out + 1) * Ct ^ Fintype.card A ∧
      ∀ (x : G → IntegerScalarCubeBox Empty S.value) (z : A → ℤ) (outPoint : Out → ZMod N),
        ‖(∑ χ : Ch, ((∏ a, (height a : ℝ)) : ℂ) *
          law.complexMean (fun y => finiteImageCharacteristic pRat
            (fun t j => (integerLongPolynomialOutput poly (fun k => (y k.1 k.2 : ℤ)) N t j : ZMod N)) χ.val *
            (if forecastInactiveFixedOutput B U basis S selected coefficients x y = (fun a _ => z a)
              then (1 : ℂ) else 0)) * star (χ.val outPoint)) -
          (∑ χ : Ch, (∑ r : Pos χ, weight χ r *
            siteFamilyEval (e χ r) (fun _ => z) (fun _ a => (z a : ℝ) / height a)) *
              star (χ.val outPoint))‖ ≤ (T : ℝ) ^ (Fintype.card Out + 1) * δout := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
