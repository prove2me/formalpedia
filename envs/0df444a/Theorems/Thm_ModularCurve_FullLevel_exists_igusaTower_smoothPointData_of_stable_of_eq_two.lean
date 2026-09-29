-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_igusaTower_smoothPointData_of_stable_of_eq_two
-- name    : ModularCurve.FullLevel.exists_igusaTower_smoothPointData_of_stable_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/a5786a66-95f4-5b02-8de2-dc5b1262ce35
-- title:
--   Igusa tower smooth-point data for q=2
-- statement:
--   Throughout, $q$ is a prime with $q=2$, $M'$ is a nonzero natural number with $q \nmid M'$, and $A$ is a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense of [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16), i.e. $q$ belongs to the non-units of $A$; write $\kappa = \mathrm{ResidueField}\,A$. Two function fields occur: the characteristic-zero field $\mathrm{fieldBar}\,q\,M' = \overline{\mathbb{Q}}\cdot F(\Gamma_H(q^2M'))$, the $\overline{\mathbb{Q}}$-base change (in the sense of `laurentBaseChange`) of the $q$-expansion function field of level $q^2M'$ with $H = \mathrm{levelH}\,q\,M'$ the kernel of the reduction $(\mathbb{Z}/q^2M')^\times \to (\mathbb{Z}/q)^\times$, that is the units congruent to $1$ modulo $q$; and its characteristic-$p$ counterpart $\bar F_H := \mathrm{xHFunctionFieldC}\,\kappa\,(q^2M')\,(\mathrm{levelH}\,q\,M')$ over $\kappa$. `Place K F` denotes a valuation subring of $F$ containing the image of $K$, different from $F$, and a principal ideal ring; `ord`, `evalAt` and `IsRational` are its order function, its $K$-valued evaluation through the residue field, and the surjectivity of $K \to$ residue field.
--
--   The data on the level-$M'$ side: a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,\kappa\,M' = \kappa(j, j_N)$ over $\kappa$, assumed by `hW` to consist exactly of the supersingular places, i.e. the rational affine geometric places $w$ with $w.\mathrm{evalAt}(\mathrm{jGeomGen}\,\kappa\,M') \in \mathrm{ssJSet}\,q\,\kappa$; an inclusion `hle` of $\overline{\mathbb{Q}}\cdot F(\Gamma_0(M'))$ (written $\mathrm{modularFunctionFieldBar}\,M'$) into $\mathrm{fieldBar}\,q\,M'$; and a constant reduction $R_0$ of $A$ from $\overline{\mathbb{Q}}\cdot F(\Gamma_0(M'))$ to $\kappa(j,j_N)$, that is, a valuation subring $R_0.\mathrm{integers}$, a surjective residue homomorphism onto $\kappa(j,j_N)$ with kernel the maximal ideal, a place map, compatibility of the integers and of the residue with $A$ and with constants, the scaling property `exists_smul_mem`, preservation of degrees of places and the divisor-pushforward identity. The hypothesis `hR₀` demands that $R_0$ be the coefficientwise reduction: for every Laurent series $y$ over $A$ whose image in $\mathrm{LaurentSeries}\,\overline{\mathbb{Q}}$ lies in $\overline{\mathbb{Q}}\cdot F(\Gamma_0(M'))$, that element lies in $R_0.\mathrm{integers}$ and its $R_0$-residue, read as a Laurent series over $\kappa$, is the coefficientwise reduction of $y$.
--
--   Further data: a primitive $q$-th root of unity $\zeta$ in $\overline{\mathbb{Q}}$ (an element of $\mathrm{Idx}\,q$); a family $O^{\mathrm{Ig}}$ of valuation subrings of $\mathrm{fieldBar}\,q\,M'$ indexed by the projective line $\mathbb{P}^1(\mathbb{Z}/q)$; and a family $O^{\mathrm{ss}}$ of valuation subrings indexed by $W$. The Igusa group of hypotheses consists of: `hIg_inf`, identifying $O^{\mathrm{Ig}}(\infty)$ (at $\mathrm{lineInfty}\,q$) as the Gauss-type ring of those $f$ for which there are Laurent series $x,y$ over $A$ with the coefficientwise reduction of $y$ non-zero and $f \cdot y = x$ in $\mathrm{LaurentSeries}\,\overline{\mathbb{Q}}$; `hIg`, that every line $\ell$ is $\mathrm{redQ}\,q\,\gamma \cdot \infty$ for some $\gamma \in \Gamma_0(M')$ with $O^{\mathrm{Ig}}(\ell)$ the pullback of $O^{\mathrm{Ig}}(\infty)$ along $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma$; `hIg_inj`, injectivity of $O^{\mathrm{Ig}}$; and `hIg_perm`, that for each $\zeta'$ and each $\gamma \in \Gamma_0(M')$ the pullbacks along $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ permute the family $O^{\mathrm{Ig}}$. The supersingular group consists of: `hSS_A`, that a constant from $\overline{\mathbb{Q}}$ lies in $O^{\mathrm{ss}}_s$ exactly when it lies in $A$; `hSS_over`, that for $s \in W$ and $f \in R_0.\mathrm{integers}$ which is regular wherever $j$ is (for every place $P$ of $\overline{\mathbb{Q}}\cdot F(\Gamma_0(M'))$ over $\overline{\mathbb{Q}}$, $0 \le P.\mathrm{ord}(j)$ implies $0 \le P.\mathrm{ord}(f)$, where $j$ is the image of the $q$-expansion $\mathrm{jq}$) and whose $R_0$-residue lies in the valuation subring of $s$, the image of $f$ in $\mathrm{fieldBar}\,q\,M'$ lies in $O^{\mathrm{ss}}_s$ and, for every $a \in A$ whose residue equals $s.\mathrm{evalAt}$ of that $R_0$-residue, the difference of the image of $f$ and $a$ lies in the maximal ideal of $O^{\mathrm{ss}}_s$; `hSS_fix`, invariance of each $O^{\mathrm{ss}}_s$ under pullback by every $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$; and `hSS_tr`, the existence for each $s$ of $t \in O^{\mathrm{ss}}_s$ with $t - a$ a unit of $O^{\mathrm{ss}}_s$ for every $a \in A$.
--
--   On the Igusa branch there is a regular prolongation $R$ of $A$ from $\mathrm{fieldBar}\,q\,M'$ to $\bar F_H$ (a valuation subring with surjective residue map onto $\bar F_H$ with kernel the maximal ideal, compatible with $A$ and constants, and satisfying `exists_smul_mem`), with `hR`: $R.\mathrm{integers} = O^{\mathrm{Ig}}(\infty)$, and `hR₀O`: $f \in R_0.\mathrm{integers}$ if and only if the image of $f$ lies in $O^{\mathrm{Ig}}(\infty)$. An element $\pi \in A$ with $\pi^{q^2-1} = q$ is given.
--
--   The constant-field data: an intermediate field $k_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ and $\pi_0 \in k_0 \cap A$ such that $A \cap k_0$ (formally $A.\mathrm{comap}$ along $k_0 \to \overline{\mathbb{Q}}$) is a discrete valuation ring with maximal ideal generated by $\pi_0$, is henselian, and has algebraically closed residue field; `hκ`, that every $a \in A$ is congruent modulo the maximal ideal of $A$ to an element of $k_0 \cap A$; and `hstab`, that every automorphism $\tau$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ preserving $A$ maps $k_0$ into itself. Auxiliary prime data: a prime $\ell$ with $3 \le \ell$, $\ell \ne q$, $\ell \nmid M'$; an element $\zeta_0 \in k_0$ which is a primitive $(q\ell)$-th root of unity; and a tame element $\varpi_t \in k_0 \cap A$ with $\varpi_t^{q^2-1} = q u$ for some unit $u$ of $A$. Tower data: a type $\iota$, a family $K : \iota \to$ intermediate fields of $\overline{\mathbb{Q}}/k_0$, each finite over $k_0$, and valuation subrings $A_n$ of $K_n$ with $x \in A_n \iff x \in A$.
--
--   The conclusion, with $k_0$ acting on $\mathrm{fieldBar}\,q\,M'$ through $\overline{\mathbb{Q}}$, asserts the existence of an intermediate field $F_0$ of $\mathrm{fieldBar}\,q\,M'/k_0$, a finite set $N^{\mathrm{Ig}}$ of places of $\bar F_H$ over $\kappa$, subrings $S_{Q,n} \subseteq \mathrm{fieldBar}\,q\,M'$, ring homomorphisms $\varphi_{Q,n} : A_n[X] \to S_{Q,n}$ and $\chi_{Q,n} : S_{Q,n} \to \kappa$, and sets $D_{Q,n}$ of places of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb{Q}}$ (all indexed by places $Q$ of $\bar F_H$ over $\kappa$ and by $n \in \iota$), subject to the following conjuncts.
--
--   (i) The $k_0$-subfield generated by the image of $\overline{\mathbb{Q}}$ together with $F_0$ is all of $\mathrm{fieldBar}\,q\,M'$. (ii) $F_0$ is stable under $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ for every $\zeta' \in \mathrm{Idx}\,q$ and every $\gamma \in \Gamma_0(M')$. (iii) $|N^{\mathrm{Ig}}| = |W|$. (iv) There is a ring homomorphism $j : \kappa(j,j_N) \to \bar F_H$ such that every $f \in R_0.\mathrm{integers}$ has image in $R.\mathrm{integers}$ with $R$-residue $j(R_0.\mathrm{residue}\,f)$, and such that $Q \in N^{\mathrm{Ig}}$ if and only if there is $s \in W$ with $g$ in the valuation subring of $s$ exactly when $j(g)$ lies in that of $Q$. (v) Every valuation subring of $\mathrm{fieldBar}\,q\,M'$ containing all constants from $\overline{\mathbb{Q}}$ and different from the whole field is a principal ideal ring.
--
--   (vi) For every place $Q \notin N^{\mathrm{Ig}}$ the following hold. First, for every $n \in \iota$: (a) the reduction map $A_n \to \kappa$ is surjective; (b) the image of $A_n$ in $\mathrm{fieldBar}\,q\,M'$ lies in $S_{Q,n}$; (c) $\varphi_{Q,n}$ is formally smooth and formally unramified; (d) $\varphi_{Q,n}(C\,a)$ is the image of $a$ for $a \in A_n$, and (e) $\chi_{Q,n}(\varphi_{Q,n}(C\,a))$ is the residue of $a$ in $\kappa$; (f) $\chi_{Q,n}(\varphi_{Q,n}(X)) = 0$; (g) for every $c \in A_n$ with zero residue in $\kappa$ there is a unique ring homomorphism $\chi : S_{Q,n} \to A_n$ splitting $\varphi_{Q,n} \circ C$, reducing to $\chi_{Q,n}$ after composition with $A_n \to \kappa$, and sending $\varphi_{Q,n}(X)$ to $c$; (h) every $f \in S_{Q,n}$ lies in $R.\mathrm{integers}$, its $R$-residue lies in the valuation subring of $Q$, and the residue of the latter in the residue field of $Q$ is the image of $\chi_{Q,n}(f)$ under $\kappa \to Q.\mathrm{ResidueField}$; (i) $\varphi_{Q,n}(X)$ lies in $R.\mathrm{integers}$ and its $R$-residue has $Q$-order $1$; (j) $D_{Q,n}$ consists exactly of the rational places $P$ such that every $f \in S_{Q,n}$ lies in the valuation subring of $P$ with $P.\mathrm{evalAt}(f) \in A$, and such that $A.\mathrm{valuation}(P.\mathrm{evalAt}(f)) < 1$ if and only if $\chi_{Q,n}(f) = 0$; (k) $\varphi_{Q,n}(X) \ne \varphi_{Q,n}(C\,c)$ for every $c \in A_n$; (l) $S_{Q,n}$ is a local ring whose maximal ideal is the kernel of $\chi_{Q,n}$; (m) $S_{Q,n}$ is Noetherian and a unique factorisation monoid; (n) $S_{Q,n}$ is contained in the join $L_n := k_0(\text{image of } K_n) \sqcup F_0$ and every element of $L_n$ is a quotient $g/h$ with $g,h \in S_{Q,n}$, $h \ne 0$; (o) linear disjointness: for $c_1,\dots,c_m \in \overline{\mathbb{Q}}$ linearly independent over $K_n$ and $a_1,\dots,a_m \in L_n$ with $\sum_i c_i a_i = 0$, all $a_i$ vanish; (p) there is a uniformiser $\varpi$ of $A_n$ (generating its maximal ideal, non-zero) such that $\varphi_{Q,n}(C\,\varpi)$ is prime in $S_{Q,n}$, such that an element of $L_n$ lies in $R.\mathrm{integers}$ precisely when it is $g/h$ with $g,h \in S_{Q,n}$ and $\varphi_{Q,n}(C\,\varpi) \nmid h$, and such that for every prime $p$ of $S_{Q,n}$ not associated to $\varphi_{Q,n}(C\,\varpi)$ and every $x \in S_{Q,n}$ there is a monic $r \in A_n[X]$ with $p$ dividing the value at $x$ of $r$ pushed forward along $\varphi_{Q,n} \circ C$; (q) every ring homomorphism $\chi : S_{Q,n} \to A_n$ splitting $\varphi_{Q,n} \circ C$ and reducing to $\chi_{Q,n}$ has kernel generated by $\varphi_{Q,n}(X) - \varphi_{Q,n}(C(\chi(\varphi_{Q,n}(X))))$; (r) there is a finite subset $G \subseteq S_{Q,n}$ such that every $f \in S_{Q,n}$ is $g/h$ with $g,h$ in the subring generated by $G$ together with the image of $A_n$ and with $h$ the image of a unit of $S_{Q,n}$. Secondly, the family is monotone in $n$: whenever $K_n \le K_{n'}$ one has $S_{Q,n} \le S_{Q,n'}$, and moreover $S_{Q,n'}$ is contained in the subring generated by $S_{Q,n}$ together with the image of $A_{n'}$, the elements $\varphi_{Q,n}(X)$ agree in $\mathrm{fieldBar}\,q\,M'$ for all $n$ and $n'$, and $\chi_{Q,n'}$ restricts to $\chi_{Q,n}$ on $S_{Q,n}$.
--
--   (vii) For $Q, Q' \notin N^{\mathrm{Ig}}$, any $n$ and any place $P \in D_{Q,n} \cap D_{Q',n}$, one has $Q = Q'$. (viii) For every $\tau$ in the subgroup of $\overline{\mathbb{Q}}$-automorphisms of $\mathrm{fieldBar}\,q\,M'$ generated by the $\mathrm{levelAutBar}\,q\,M'\,\zeta'\,\gamma$ with $\gamma \in \Gamma_0(M')$, and every proof that $\tau$ preserves $R.\mathrm{integers}$, the induced automorphism $R.\mathrm{resAut}\,\tau$ of $\bar F_H$ preserves $N^{\mathrm{Ig}}$ (membership is unchanged in both directions), and for $Q \notin N^{\mathrm{Ig}}$ and every $n$ the translated disc $\mathrm{smulDisc}\,\tau\,(D_{Q,n}) = \{P \mid \tau^{-1}\cdot P \in D_{Q,n}\}$ equals $D_{R.\mathrm{resAut}\,\tau \cdot Q,\,n}$. (ix) For every $\tau$ in the inertia subgroup $A.\mathrm{inertiaSubgroupIn}\,\mathbb{Q}$, every $n$ with $\tau(K_n) \subseteq K_n$ and every $Q \notin N^{\mathrm{Ig}}$, the subring $S_{Q,n}$ is stable under the semilinear action $\mathrm{arithmeticGalois}$ of $\tau$ on $\mathrm{fieldBar}\,q\,M'$ (membership holds for $f$ iff it holds for its translate) and $\chi_{Q,n}$ is unchanged by that action. (x) For every $g$ in the same subgroup generated by the level automorphisms, if the pullback of $O^{\mathrm{Ig}}(\infty)$ along $g$ differs from $O^{\mathrm{Ig}}(\infty)$, then for $Q, Q' \notin N^{\mathrm{Ig}}$, every $n$ and every $P \in D_{Q,n}$, the place $g \cdot P$ does not lie in $D_{Q',n}$.
--
--   (xi) For $Q \notin N^{\mathrm{Ig}}$, every $n$, every $P \in D_{Q,n}$ and every $s \in W$, it is not the case that both of the following hold: the image of $j$ (the element $\mathrm{coeffEmb}\,\overline{\mathbb{Q}}\,\mathrm{jq}$) lies in the valuation subring of $P$ and, for every $a \in A$ whose residue equals $s.\mathrm{evalAt}(\mathrm{jGeomGen}\,\kappa\,M')$, the difference $P.\mathrm{evalAt}(j) - a$ lies in the maximal ideal of $A$; and the same two conditions for the image of $\mathrm{qExpand}\,\mathbb{Q}\,M'\,\mathrm{jq}$ with $\mathrm{jNGeomGen}\,\kappa\,M'$ in place of $\mathrm{jGeomGen}\,\kappa\,M'$. (xii) For every place $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb{Q}}$: if for no $s \in W$ does $P$ satisfy the supersingular-specialisation condition — namely that for every $f \in R_0.\mathrm{integers}$ regular wherever $j$ is and with $R_0$-residue in the valuation subring of $s$, and every $a \in A$ whose residue is $s.\mathrm{evalAt}$ of that residue, the difference $P.\mathrm{evalAt}$ of the image of $f$ minus $a$ lies in the maximal ideal of $A$ — then there are $\gamma \in \Gamma_0(M')$ and $Q \notin N^{\mathrm{Ig}}$ with $\mathrm{levelAutBar}\,q\,M'\,\zeta\,\gamma \cdot P \in D_{Q,n}$ for every $n$. (xiii) Finally, there is a place $P$ of $\mathrm{fieldBar}\,q\,M'$ over $\overline{\mathbb{Q}}$ whose valuation subring is $\mathrm{qIntegersBar}\,\overline{\mathbb{Q}}\,(\mathrm{fieldBar}\,q\,M')$, the ring of elements of non-negative Laurent order, together with a $Q \notin N^{\mathrm{Ig}}$ such that $P \in D_{Q,n}$ for every $n$.
--
--   This is the $q=2$ case of the construction of smooth-point chart data on the Igusa branch of the semistable covering of the modular curve of level $q^2M'$ with $H$ the units congruent to $1$ modulo $q$: it produces, at every finite layer $K_n$ of constants, local models $S_{Q,n}$ with their formal parameter $\varphi_{Q,n}(X)$, reduction $\chi_{Q,n}$, and residue discs $D_{Q,n}$, compatibly with the level automorphisms and with the inertia action, and identifies the excluded places as those lying over the supersingular places of level $M'$. It feeds the subsequent assembly of Igusa smooth-point charts from a Gauss ring with the full inertia clause at $q=2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_igusaTower_smoothPointData_of_stable_of_eq_two.lean

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_ResidueDiscs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.FullLevel.exists_igusaTower_smoothPointData_of_stable_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (ζ : Idx q)
    (OIg : CuspidalType.ProjLine q → ValuationSubring (fieldBar q M'))
    (OSS : ↥W → ValuationSubring (fieldBar q M'))

    (hIg_inf : ∀ f : fieldBar q M', f ∈ OIg (lineInfty q) ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (hIg : ∀ ℓ, ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ redQ q γ • lineInfty q = ℓ ∧
      OIg ℓ = (OIg (lineInfty q)).comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom)
    (hIg_inj : Function.Injective OIg)
    (hIg_perm : ∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      ∃ σ : Equiv.Perm (CuspidalType.ProjLine q),
        ∀ ℓ, (OIg ℓ).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OIg (σ ℓ))

    (hSS_A : ∀ s (x : AlgebraicClosure ℚ), algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ OSS s ↔ x ∈ A)
    (hSS_over : ∀ (s : ↥W) (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
          ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
        (IntermediateField.inclusion hle f : fieldBar q M') ∈ OSS s ∧
        ∀ a : A, residue A a =
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
          ∃ h : (IntermediateField.inclusion hle f : fieldBar q M')
              - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s,
            (⟨_, h⟩ : OSS s) ∈ maximalIdeal (OSS s))
    (hSS_fix : ∀ (s : ↥W) (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
      (OSS s).comap (levelAutBar q M' ζ' γ).toAlgHom.toRingHom = OSS s)

    (hSS_tr : ∀ s : ↥W, ∃ t : fieldBar q M', t ∈ OSS s ∧ ∀ a : A,
      ∃ h : t - algebraMap (AlgebraicClosure ℚ) (fieldBar q M') (a : AlgebraicClosure ℚ) ∈ OSS s, IsUnit (⟨_, h⟩ : OSS s))
    (R : RegularProlongation A (fieldBar q M') (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) (hR : R.integers = OIg (lineInfty q))
    (hR₀O : ∀ f : ↥(modularFunctionFieldBar M'), f ∈ R₀.integers ↔
      (IntermediateField.inclusion hle f : fieldBar q M') ∈ OIg (lineInfty q))

    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ A)

    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ₀ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ₀⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A)

    (hstab : ∀ τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), (∀ x : (AlgebraicClosure ℚ), x ∈ A ↔ τ x ∈ A) →
      ∀ x : (AlgebraicClosure ℚ), x ∈ k₀ → τ x ∈ k₀)

    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (ζ₀ : ↥k₀) (hζ₀ : IsPrimitiveRoot ((ζ₀ : ↥k₀) : AlgebraicClosure ℚ) (q * ℓ))
    (ϖt : ↥k₀) (hϖtA : (ϖt : AlgebraicClosure ℚ) ∈ A)
    (hϖt : ∃ u : ↥A, IsUnit u ∧ (ϖt : AlgebraicClosure ℚ) ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) * (u : AlgebraicClosure ℚ))

    {ι : Type} (K : ι → IntermediateField ↥k₀ (AlgebraicClosure ℚ)) (hKfin : ∀ n, FiniteDimensional ↥k₀ ↥(K n))
    (An : ∀ n, ValuationSubring ↥(K n))
    (hAn : ∀ n (x : ↥(K n)), x ∈ An n ↔ (x : AlgebraicClosure ℚ) ∈ A) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∃ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M'))
      (NIg : Finset (Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))))
      (Sn : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → ι → Subring ↥(fieldBar q M'))
      (φn : (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) → (n : ι) → (Polynomial ↥(An n) →+* ↥(Sn Q n)))
      (χn : (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))) → (n : ι) → (↥(Sn Q n) →+* ResidueField ↥A))
      (Dn : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')) → ι → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),

      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) ∧
      (∀ (ζ' : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' → ∀ f : ↥(fieldBar q M'), f ∈ F₀ → levelAutBar q M' ζ' γ f ∈ F₀) ∧

      NIg.card = W.card ∧

      (∃ j : modularFunctionFieldC (ResidueField A) M' →+* xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'),
        (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers, R.residue ⟨_, hC⟩ = j (R₀.residue ⟨f, hf⟩)) ∧
        ∀ Q, Q ∈ NIg ↔ ∃ s : ↥W, ∀ g : modularFunctionFieldC (ResidueField A) M',
          g ∈ (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ↔
            j g ∈ Q.toValuationSubring) ∧

      (∀ O : ValuationSubring ↥(fieldBar q M'), (∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') x ∈ O) → O ≠ ⊤ → IsPrincipalIdealRing ↥O) ∧

      (∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg →
            (∀ n : ι,

              Function.Surjective (fun a : ↥(An n) => IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : AlgebraicClosure ℚ), (hAn n a).mp a.2⟩) ∧

              (∀ a : ↥(An n), algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ) ∈ Sn Q n) ∧

              (φn Q n).FormallySmooth ∧ (φn Q n).FormallyUnramified ∧

              (∀ a : ↥(An n), ((φn Q n (Polynomial.C a) : ↥(Sn Q n)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) ∧

              (∀ a : ↥(An n), χn Q n (φn Q n (Polynomial.C a)) = IsLocalRing.residue ↥A ⟨((a : ↥(K n)) : AlgebraicClosure ℚ), (hAn n a).mp a.2⟩) ∧

              χn Q n (φn Q n Polynomial.X) = 0 ∧

              (∀ c : ↥(An n), IsLocalRing.residue ↥A ⟨((c : ↥(K n)) : AlgebraicClosure ℚ), (hAn n c).mp c.2⟩ = 0 →
                ∃! χ : ↥(Sn Q n) →+* ↥(An n), (∀ a : ↥(An n), χ (φn Q n (Polynomial.C a)) = a) ∧
                  (∀ f : ↥(Sn Q n), IsLocalRing.residue ↥A ⟨((χ f : ↥(K n)) : AlgebraicClosure ℚ), (hAn n _).mp (χ f).2⟩ = χn Q n f) ∧
                  χ (φn Q n Polynomial.X) = c) ∧

              (∀ f : ↥(Sn Q n), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
                IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                  algebraMap (ResidueField ↥A) Q.ResidueField (χn Q n f)) ∧

              (∃ hR : ((φn Q n Polynomial.X : ↥(Sn Q n)) : ↥(fieldBar q M')) ∈ R.integers,
                Q.ord (R.residue ⟨((φn Q n Polynomial.X : ↥(Sn Q n)) : ↥(fieldBar q M')), hR⟩) = 1) ∧

              (∀ P, P ∈ Dn Q n ↔ (P.IsRational ∧
                (∀ f : ↥(Sn Q n), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
                (∀ f : ↥(Sn Q n), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χn Q n f = 0))) ∧

              (∀ c : ↥(An n), φn Q n Polynomial.X ≠ φn Q n (Polynomial.C c)) ∧

              (∃ _ : IsLocalRing ↥(Sn Q n), ∀ f : ↥(Sn Q n), f ∈ IsLocalRing.maximalIdeal ↥(Sn Q n) ↔ χn Q n f = 0) ∧

              IsNoetherianRing ↥(Sn Q n) ∧ UniqueFactorizationMonoid ↥(Sn Q n) ∧

              (∀ f : ↥(fieldBar q M'), f ∈ Sn Q n → f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀) ∧
              (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀ → ∃ g h : ↥(Sn Q n), (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧

              (∀ (m : ℕ) (c : Fin m → AlgebraicClosure ℚ) (a : Fin m → ↥(fieldBar q M')), (∀ i, a i ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀) →
                LinearIndependent ↥(K n) c → ∑ i, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (c i) * a i = 0 → ∀ i, a i = 0) ∧

              (∃ ϖ : ↥(An n), IsLocalRing.maximalIdeal ↥(An n) = Ideal.span {ϖ} ∧ ϖ ≠ 0 ∧
                Prime (φn Q n (Polynomial.C ϖ)) ∧
                (∀ f : ↥(fieldBar q M'), f ∈ IntermediateField.adjoin ↥k₀ (⇑(algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')) '' (↑(K n) : Set (AlgebraicClosure ℚ))) ⊔ F₀ →
                  (f ∈ R.integers ↔ ∃ g h : ↥(Sn Q n), ¬ (φn Q n (Polynomial.C ϖ) ∣ h) ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M')))) ∧
                (∀ p : ↥(Sn Q n), Prime p → ¬ Associated p (φn Q n (Polynomial.C ϖ)) →
                  ∀ x : ↥(Sn Q n), ∃ r : Polynomial ↥(An n), r.Monic ∧ p ∣ (r.map ((φn Q n).comp Polynomial.C)).eval x)) ∧

              (∀ χ : ↥(Sn Q n) →+* ↥(An n), (∀ a : ↥(An n), χ (φn Q n (Polynomial.C a)) = a) →
                (∀ f : ↥(Sn Q n), IsLocalRing.residue ↥A ⟨((χ f : ↥(K n)) : AlgebraicClosure ℚ), (hAn n _).mp (χ f).2⟩ = χn Q n f) →
                RingHom.ker χ = Ideal.span {φn Q n Polynomial.X - φn Q n (Polynomial.C (χ (φn Q n Polynomial.X)))}) ∧

              (∃ G : Finset ↥(fieldBar q M'), ↑G ⊆ (Sn Q n : Set ↥(fieldBar q M')) ∧ ∀ f ∈ Sn Q n, ∃ g h : ↥(fieldBar q M'),
                g ∈ Subring.closure (↑G ∪ ((fun a : ↥(An n) => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) '' Set.univ)) ∧
                h ∈ Subring.closure (↑G ∪ ((fun a : ↥(An n) => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n)) : AlgebraicClosure ℚ)) '' Set.univ)) ∧
                (∃ u : (↥(Sn Q n))ˣ, ((u : ↥(Sn Q n)) : ↥(fieldBar q M')) = h) ∧ f * h = g)) ∧

            (∃ hmono : ∀ n n', K n ≤ K n' → Sn Q n ≤ Sn Q n',
              (∀ n n', K n ≤ K n' →
                Sn Q n' ≤ Subring.closure ((Sn Q n : Set ↥(fieldBar q M')) ∪ ((fun a : ↥(An n') => algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') ((a : ↥(K n')) : AlgebraicClosure ℚ)) '' Set.univ))) ∧
              (∀ n n', ((φn Q n Polynomial.X : ↥(Sn Q n)) : ↥(fieldBar q M')) = ((φn Q n' Polynomial.X : ↥(Sn Q n')) : ↥(fieldBar q M'))) ∧
              (∀ n n' (h : K n ≤ K n') (f : ↥(Sn Q n)), χn Q n' ⟨(f : ↥(fieldBar q M')), hmono n n' h f.2⟩ = χn Q n f))) ∧

          (∀ Q Q' : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg → Q' ∉ NIg → ∀ (n : ι) (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), P ∈ Dn Q n → P ∈ Dn Q' n → Q = Q') ∧

          (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M'))),
              (R.resAut τ hτ • Q ∈ NIg ↔ Q ∈ NIg) ∧
              (Q ∉ NIg → ∀ n : ι, AlgebraicCurve.RegularProlongation.smulDisc τ (Dn Q n) = Dn (R.resAut τ hτ • Q) n)) ∧

          (∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ n : ι, (∀ x : AlgebraicClosure ℚ, x ∈ K n → τ x ∈ K n) →
            ∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg →
              (∀ f : ↥(fieldBar q M'), f ∈ Sn Q n ↔ ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • f ∈ Sn Q n) ∧
              (∀ (f : ↥(Sn Q n)) (hf : ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : ↥(fieldBar q M')) ∈ Sn Q n),
                χn Q n ⟨ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ • (f : ↥(fieldBar q M')), hf⟩ = χn Q n f)) ∧

          (∀ g ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
              ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
            (OIg (lineInfty q)).comap g.toAlgHom.toRingHom ≠ OIg (lineInfty q) →
              ∀ Q Q' : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg → Q' ∉ NIg → ∀ (n : ι) (P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M')), P ∈ Dn Q n → g • P ∉ Dn Q' n) ∧

          (∀ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg → ∀ (n : ι), ∀ P ∈ Dn Q n, ∀ s : ↥W, ¬ (((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ P.toValuationSubring ∧
              (∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jGeomGen (ResidueField A) M') →
                ∃ h : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                  (⟨_, h⟩ : A) ∈ maximalIdeal A)) ∧
            ((IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') ∈ P.toValuationSubring ∧
              (∀ a : A, residue A a = (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (jNGeomGen (ResidueField A) M') →
                ∃ h : P.evalAt (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq),
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jqN_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                  (⟨_, h⟩ : A) ∈ maximalIdeal A)))) ∧

          (∀ P : Place (AlgebraicClosure ℚ) (fieldBar q M'),
            (∀ s : ↥W, ¬ (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
                (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
                  0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
                    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
                    ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
                (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
                    (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
                  ∀ a : A, residue A a =
                      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) →
                    ∃ h : P.evalAt (IntermediateField.inclusion hle f : fieldBar q M') - (a : AlgebraicClosure ℚ) ∈ A,
                      (⟨_, h⟩ : A) ∈ maximalIdeal A)) →
            ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ ∃ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg ∧ ∀ n : ι, levelAutBar q M' ζ γ • P ∈ Dn Q n) ∧

          (∃ P : Place (AlgebraicClosure ℚ) (fieldBar q M'), P.toValuationSubring = qIntegersBar (AlgebraicClosure ℚ) (fieldBar q M') ∧
            ∃ Q : Place (ResidueField A) (xHFunctionFieldC (ResidueField A) (q ^ 2 * M') (levelH q M')), Q ∉ NIg ∧ ∀ n : ι, P ∈ Dn Q n) := by sorry
