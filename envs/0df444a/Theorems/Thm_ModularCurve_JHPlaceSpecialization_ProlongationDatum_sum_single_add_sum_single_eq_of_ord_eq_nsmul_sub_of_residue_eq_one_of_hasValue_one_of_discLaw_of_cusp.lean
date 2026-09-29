-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_residue_eq_one_of_hasValue_one_of_discLaw_of_cusp
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_residue_eq_one_of_hasValue_one_of_discLaw_of_cusp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/f8cb5836-6a3f-5ce7-b40e-758bdf8b79d7
-- title:
--   Rigidity of the base divisor for normalised bi-integral functions
-- statement:
--   Setting. Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ (`hpM`) and $p^2 \nmid M$ (`hpM2`), and let $H \le (\mathbb{Z}/M)^{\times}$ be a subgroup which, by `hHp`, contains every unit reducing to $1$ under `ZMod.unitsMap` for $M/p \mid M$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $A.\mathrm{LiesOverPrime}\ p$, i.e. $p$ lies in the nonunits of $A$, and assume its residue field $\kappa = \mathrm{ResidueField}\ A$ is algebraically closed of characteristic $p$. Write $F_M$ for `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$ of the $X_H(M)$-function field inside $\overline{\mathbb{Q}}$-Laurent series, $F_{M/p}$ for `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)`, where `infSubgroup` is the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$, and $\bar F$ for `JHNeronObjectAtP.Fbar p M H hpM κ`, the $q$-expansion function field over $\kappa$ for the group `JHNeronObjectAtP.ΓN p M H hpM`. Places are taken in the project's sense (a valuation subring of the function field, not the whole field, containing the image of the base field and with principal ideals), $\mathrm{ord}_v$ is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation, $v.\mathrm{HasValue}\ g\ a$ means $g$ lies in the valuation ring and reduces to the image of $a$ in the residue field of $v$, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places.
--
--   Morphisms. Let $\theta$ be a $\overline{\mathbb{Q}}$-automorphism of $F_M$ and let $\alpha, \beta \colon F_{M/p} \to F_M$ be $\overline{\mathbb{Q}}$-algebra maps which are integral (`hα`, `hβ`). The hypothesis `hα_coe` says that $\alpha$ is the identity on underlying Laurent series, `hβ_coe` that $\beta$ acts on Laurent series as `qExpand _ p` (substitution $q \mapsto q^{p}$), `hβθ` that $\beta = \theta \circ \alpha$, and `hθgal` that $\theta$ commutes with the arithmetic Galois action `arithmeticGalois` of $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ on $F_M$.
--
--   Diamond operator and supersingular nodes. Let $pb$ be a unit of $\mathbb{Z}/(M/p)$ whose underlying element is $p$ (`hpb`), and let $\delta$ be a self-map of the set of places of $\bar F$ over $\kappa$ which, by `hδ`, is the action of the semilinear automorphism attached to the diamond automorphism `diamondActionModL κ (M/p) (infSubgroup p M H hpM)` evaluated at the $\Gamma_0(M/p)$-lift [`CuspForm.gammaLift (M/p) pb`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36). Let $SS$ be a finset of pairs of places of $\bar F$ whose members are, by `hSS`, exactly the elements of `ssNodePairsQExp κ (ΓN p M H hpM) p`, that is the pairs $s$ with $s.2$ supersingular and $s.1$ the modular Frobenius place `qExpFrobeniusPlaceModL` of $s.2$.
--
--   Specialisation data and laws. Let `Psp` be a `JHPlaceSpecialization p M H hpM A`, so a map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\bar F$ together with a homomorphism on degree-zero divisor classes and the compatibilities recorded in that structure ($q$-expansion compatibility of divisors, surjectivity, existence of specialised functions, invariance under inertia, Frobenius equivariance, and compatibility on $\mathrm{Pic}^0$). For a place $W$ of $F_M$ put $\mathrm{reduceFst}\ W = \mathrm{sp}(W|_{\alpha})$ and $\mathrm{reduceSnd}\ W = \delta(\mathrm{sp}(W|_{\beta}))$, restriction being along the integral maps $\alpha$, $\beta$; $W$ is of strict first kind when $\delta(\mathrm{Frob}(\mathrm{reduceFst}\ W)) = \mathrm{reduceSnd}\ W$ and $\mathrm{reduceFst}\ W$ is not `Fixed` (where $v$ is `Fixed` when $\mathrm{Frob}(\delta(\mathrm{Frob}\ v)) = v$), and of strict second kind when $\mathrm{reduceFst}\ W = \mathrm{Frob}(\mathrm{reduceSnd}\ W)$ and $\mathrm{reduceSnd}\ W$ is not `Fixed`. A place $v$ of $\bar F$ is an affine place when some $x$ with Laurent series `jqModC κ` has a value at $v$. Let `Rpd` be a `ProlongationDatum` for `Psp` and $\theta$: two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with values in $\bar F$, together with the $q$-expansion compatibility of $R_1$-residues and the identifications $f \in R_2 \iff \theta f \in R_1$ and $R_2$-residue of $f$ equal to the $R_1$-residue of $\theta f$. The hypotheses on these data are: `hTD`, the dichotomy that every place $W$ of $F_M$ satisfies $\mathrm{reduceFst}\ W = \mathrm{Frob}(\mathrm{reduceSnd}\ W)$ or $\delta(\mathrm{Frob}(\mathrm{reduceFst}\ W)) = \mathrm{reduceSnd}\ W$; `hmodel`, the conjunction of the two divisor laws (for bi-integral $f$ with nonzero residues, the push-forward along $\mathrm{reduceFst}$ of the strict-first-kind part of $\operatorname{div} f$ computes $\mathrm{ord}$ of the $R_1$-residue at non-`Fixed` places, and symmetrically on the second side) and the two cusp laws (the analogous statements for the infinity-side and zero-side parts of $\operatorname{div} f$ at reductions of such cusps); `hO`, the order law at `Fixed` affine places, where the push-forward of $\operatorname{div} f$ is the sum of the order of the $R_1$-residue at $v$ and of the $R_2$-residue at $\delta(\mathrm{Frob}\ v)$; `hRL`, the regularity law for $SS$ (nonnegativity of the residue orders at `Fixed` affine places, and existence of a common value of the two residues at the two places of each node pair, under nonnegativity of $\mathrm{ord} f$ above); and `hNV`, the node value law for $SS$ (a nonzero common value of the two residues at each node pair not met by the divisor of $f$).
--
--   Polar laws at strict places. The hypotheses `hLFst` and `hLSnd` are two mirror-image conditions, on the first and second side respectively. In the first, for all distinct strict-first-kind places $Q, Q'$ with equal and affine first reduction, all $n$ nonzero in $\kappa$, all $g$ in the integers of $R_1$ with nonzero $R_1$-residue such that $\mathrm{ord}_Q g = -n$, $\mathrm{ord}_{Q'} g = n$ and $\mathrm{ord}_W g = 0$ for every other strict-first-kind $W$ with the same first reduction, and all $e \in A$ and $\varepsilon$ in the integers of $R_1$ with nonzero residue such that $g = 1 + e\,\varepsilon$, the conclusion is $-1 \le \mathrm{ord}_{\mathrm{reduceFst}\,Q}$ of the $R_1$-residue of $\varepsilon$. The hypothesis `hLSnd` is the same statement with strict second kind, $\mathrm{reduceSnd}$ and $R_2$ throughout.
--
--   Modular units. The hypothesis `hUnit` asserts the existence of $u_1, u_2 \in F_M$ and divisors $D_1, D_2$ with $D_1 = \operatorname{div} u_1$ and $D_2 = \operatorname{div} u_2$ such that: $u_1$ and $u_1^{-1}$ lie in the integers of $R_1$ with nonzero $R_1$-residue, the push-forward along $\mathrm{reduceFst}$ of the strict-first-kind part of $D_1$ agrees with the order of that residue at every non-`Fixed` place, and the push-forward of the infinity-side part of $D_1$ agrees with it at the first reduction of every infinity-side place; every nonzero $f \in F_M$ admits $m \ne 0$ and $j \in \mathbb{Z}$ with $f^{m} u_1^{j}$ in the integers of $R_2$ of nonzero residue; and the mirror-image statements for $u_2$, $D_2$, $\mathrm{reduceSnd}$, the strict-second-kind and zero-side parts, $R_2$, together with the corresponding normalisability of every nonzero $f$ by powers of $u_2$ into $R_1$. Here infinity-side places are the cuspidal places (those at which $x - a$ has nonpositive order for every $x$ with Laurent series `jqModC` and every $a \in A$) carrying a value $\tau$ with residue $1$ of $x'/x^{p}$, and zero-side places are defined in the same way with `jqModC` replaced by its $p$-fold $q$-expansion and the ratio $x/x'^{p}$. The hypothesis `hcusp` asserts that every non-affine place $w$ of $\bar F$ is the first reduction of some infinity-side place and the second reduction of some zero-side place.
--
--   Configuration of places. Let $d_1, d_2 \in \mathbb{N}$ and let $Q_1 \colon \mathrm{Fin}\ d_1 \to$ places of $F_M$ and $Q_2 \colon \mathrm{Fin}\ d_2 \to$ places of $F_M$ be families of strict first kind and strict second kind respectively (`hQ₁`, `hQ₂`), with $i \mapsto \mathrm{reduceFst}(Q_1 i)$ and $j \mapsto \mathrm{reduceSnd}(Q_2 j)$ injective (`hinj₁`, `hinj₂`). Let $Q_1'$, $Q_2'$ be further families of the same sizes, again of strict first and second kind (`hQ₁'`, `hQ₂'`), with $\mathrm{reduceFst}(Q_1' i) = \mathrm{reduceFst}(Q_1 i)$ and $\mathrm{reduceSnd}(Q_2' j) = \mathrm{reduceSnd}(Q_2 j)$ for all $i, j$ (`hred₁`, `hred₂`). Let $T_1, T_2$ be the finsets of places of $\bar F$ consisting exactly of the $\mathrm{reduceFst}(Q_1 i)$ and of the $\mathrm{reduceSnd}(Q_2 j)$ (`hT₁`, `hT₂`), with $T_1$ disjoint from the image of $SS$ under the first projection (`hT₁W`) and all members of $T_1$ and of $T_2$ affine places (`hT₁aff`, `hT₂aff`). Two general position hypotheses are imposed: `hgp₁`, that any $h \in \bar F$ with $\mathrm{ord}_v h \ge 0$ for $v \notin T_1$, $\mathrm{ord}_v h \ge -1$ for $v \in T_1$, and value $0$ at every $w$ in the first projection of $SS$, is zero; and `hgp₂`, that any $h \in \bar F$ with $\mathrm{ord}_v h \ge 0$ for $v \notin T_2$ and $\mathrm{ord}_v h \ge -1$ for $v \in T_2$ lies in the image of $\kappa$. Finally let $Q_s$ be a further place of strict first kind whose first reduction differs from $\mathrm{reduceFst}(Q_1 i)$ for every $i$ (`hQs`, `hQs'`), and let $n \in \mathbb{N}$ have nonzero image in $\kappa$ (`hn`).
--
--   The normalised function. Let $f_2 \in F_M$ lie in the integers of both $R_1$ and $R_2$, with $R_1$-residue and $R_2$-residue both equal to $1$ (`hres₁`, `hres₂`), with $Q_s.\mathrm{HasValue}\ f_2\ 1$ (`hval`), and with
--   $$\mathrm{ord}_V f_2 = n \Bigl( \bigl(\textstyle\sum_i [Q_1' i] + \sum_j [Q_2' j]\bigr) - \bigl(\sum_i [Q_1 i] + \sum_j [Q_2 j]\bigr) \Bigr)(V)$$
--   for every place $V$ of $F_M$ (`hdiv`), the brackets denoting `Finsupp.single` at the indicated place with coefficient $1$.
--
--   Conclusion. Then the two divisors coincide:
--   $$\sum_i [Q_1' i] + \sum_j [Q_2' j] \;=\; \sum_i [Q_1 i] + \sum_j [Q_2 j].$$
--
--   This is the rigidity step in the analysis of places on $X_H(M)$ at a prime $p$ exactly dividing $M$: a configuration of strict base points cannot be moved within its reduction classes by a divisor relation whose function is normalised (bi-integral with both residues $1$ and value $1$ at an auxiliary strict place). It is used by the variant of the rigidity theorem in which the normalisation of the function is produced from an arbitrary one, [`ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_gammaLift_of_discLaw_of_unit_of_cusp`](thm.html#ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_gammaLift_of_discLaw_of_unit_of_cusp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_residue_eq_one_of_hasValue_one_of_discLaw_of_cusp.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups Classical

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_residue_eq_one_of_hasValue_one_of_discLaw_of_cusp
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS) (hNV : Rpd.NodeValueLaw α β hα hβ δ SS)

    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α β hα hβ δ Q → Psp.IsStrictFst α β hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α β hα hβ δ Q → Psp.IsStrictSnd α β hα hβ δ Q' →
      Psp.reduceSnd β hβ δ Q' = Psp.reduceSnd β hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd β hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α β hα hβ δ W → Psp.reduceSnd β hβ δ W = Psp.reduceSnd β hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd β hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd β hβ δ C) =
            (Psp.reduceSnd β hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd β hβ δ C = w))

    {d₁ d₂ : ℕ} (Q₁ : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂ : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hQ₁ : ∀ i, Psp.IsStrictFst α β hα hβ δ (Q₁ i)) (hQ₂ : ∀ j, Psp.IsStrictSnd α β hα hβ δ (Q₂ j))
    (hinj₁ : Function.Injective fun i => Psp.reduceFst α hα (Q₁ i))
    (hinj₂ : Function.Injective fun j => Psp.reduceSnd β hβ δ (Q₂ j))
    (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hQ₁' : ∀ i, Psp.IsStrictFst α β hα hβ δ (Q₁' i)) (hQ₂' : ∀ j, Psp.IsStrictSnd α β hα hβ δ (Q₂' j))
    (hred₁ : ∀ i, Psp.reduceFst α hα (Q₁' i) = Psp.reduceFst α hα (Q₁ i))
    (hred₂ : ∀ j, Psp.reduceSnd β hβ δ (Q₂' j) = Psp.reduceSnd β hβ δ (Q₂ j))
    {T₁ T₂ : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))}
    (hT₁ : ∀ v, v ∈ T₁ ↔ ∃ i, Psp.reduceFst α hα (Q₁ i) = v) (hT₂ : ∀ v, v ∈ T₂ ↔ ∃ j, Psp.reduceSnd β hβ δ (Q₂ j) = v)
    (hT₁W : Disjoint T₁ (SS.image Prod.fst))
    (hT₁aff : ∀ v ∈ T₁, JHPlaceSpecialization.IsAffinePlace p M H hpM A v) (hT₂aff : ∀ v ∈ T₂, JHPlaceSpecialization.IsAffinePlace p M H hpM A v)
    (hgp₁ : ∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) → (∀ w ∈ (SS.image Prod.fst), w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) → ∃ c : (ResidueField ↥A), h = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c)
    (Qs : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQs : Psp.IsStrictFst α β hα hβ δ Qs) (hQs' : ∀ i, Psp.reduceFst α hα Qs ≠ Psp.reduceFst α hα (Q₁ i))
    (n : ℕ) (hn : (n : (ResidueField ↥A)) ≠ 0)

    (f₂ : ↥(xHFunctionFieldBar M H)) (h₁ : f₂ ∈ Rpd.R₁.integers) (h₂ : f₂ ∈ Rpd.R₂.integers)
    (hres₁ : Rpd.R₁.residue ⟨f₂, h₁⟩ = 1) (hres₂ : Rpd.R₂.residue ⟨f₂, h₂⟩ = 1)
    (hval : Qs.HasValue f₂ (1 : AlgebraicClosure ℚ))
    (hdiv : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord f₂ = (n : ℤ) * (((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ))
          - (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ)) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V)) :
    (∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
      ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) := by sorry
