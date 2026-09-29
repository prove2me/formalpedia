-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_igusaTower_smoothPointData_of_stable
-- name    : ModularCurve.FullLevel.exists_igusaTower_smoothPointData_of_stable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/ed86e6ec-4aaf-5c9d-8502-dcb8c02a459b
-- title:
--   Igusa smooth-point data at each layer of a constants tower
-- statement:
--   **Setting.** Let $q\ge 5$ be a prime and $M'$ a positive integer with $q\nmid M'$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with `hA : A.LiesOverPrime q`, that is, $q$ lies in `A.nonunits`; write $\kappa=$ `ResidueField A`. Let $W$ be a finite set of places of $\kappa(j,j_{M'})=$ `modularFunctionFieldC κ M'` over $\kappa$, and `hW` requires that $W$ consist exactly of the elements of `ssPlaces q M' κ`, i.e. of those places $w$ that are rational, satisfy the predicate `IsAffineGeomPlace`, and have $w.\mathrm{evalAt}$ of the generator `jGeomGen κ M'` in `ssJSet q κ`. Let $F=$ `fieldBar q M'` be the base change to $\overline{\mathbb Q}$ of the $q$-expansion function field of level $\Gamma_H(q^2M')$ with $H=$ `levelH q M'` the kernel of the reduction map of unit groups given by `dvd_sq_mul q M'`, and let `hle` give the inclusion of `modularFunctionFieldBar M'` (the base change to $\overline{\mathbb Q}$ of `modularFunctionFieldFull M'`) into $F$. Let $R_0$ be a `ConstantReduction` of $A$ from `modularFunctionFieldBar M'` to `modularFunctionFieldC κ M'`: a valuation subring $R_0.\mathrm{integers}$, a surjective reduction homomorphism onto $\kappa(j,j_{M'})$ with kernel the maximal ideal, a map on places preserving degrees and compatible with divisor push-forward, the compatibility of the inclusion of constants with $A$ and with the residue map of $A$, and the existence, for each nonzero element, of a constant scaling it into the integers with nonzero residue. The hypothesis `hR₀` requires that every Laurent series $y$ with coefficients in $A$ whose image in `LaurentSeries (AlgebraicClosure ℚ)` lies in `modularFunctionFieldBar M'` belongs to $R_0.\mathrm{integers}$ and has $R_0$-residue the coefficientwise reduction of $y$. Finally let $\zeta$ be an element of `Idx q`, i.e. a primitive $q$-th root of unity in $\overline{\mathbb Q}$.
--
--   **Igusa and supersingular rings.** Two families of valuation subrings of $F$ are given: $O^{\mathrm{Ig}}=$ `OIg` indexed by $\mathbb P^1(\mathbb F_q)=$ [`CuspidalType.ProjLine q`](def/CuspidalType_IsCuspidalOfType.html#L21), and $O^{\mathrm{ss}}=$ `OSS` indexed by $W$. The hypothesis `hIg_inf` identifies $O^{\mathrm{Ig}}(\infty)$, at the line `lineInfty q` spanned by $(1,0)$, as the set of $f\in F$ for which there are Laurent series $x,y$ with coefficients in $A$, the coefficientwise reduction of $y$ nonzero, with $f\cdot y=x$ in `LaurentSeries (AlgebraicClosure ℚ)`. The hypothesis `hIg` requires that each line $\ell$ be of the form `redQ q γ • lineInfty q` for some $\gamma\in\Gamma_0(M')$ with $O^{\mathrm{Ig}}(\ell)$ the preimage of $O^{\mathrm{Ig}}(\infty)$ under `levelAutBar q M' ζ γ`; `hIg_inj` requires `OIg` to be injective; `hIg_perm` requires that for every $\zeta'\in$ `Idx q` and every $\gamma\in\Gamma_0(M')$ the preimages of the $O^{\mathrm{Ig}}(\ell)$ under `levelAutBar q M' ζ' γ` permute the family, by a permutation $\sigma$ of $\mathbb P^1(\mathbb F_q)$.
--
--   The hypothesis `hSS_A` requires that, for each $s\in W$, an element of $\overline{\mathbb Q}$ lie in $O^{\mathrm{ss}}(s)$ precisely when it lies in $A$. The hypothesis `hSS_over` requires: for $s\in W$ and $f\in R_0.\mathrm{integers}$ of nonnegative order at every place of `modularFunctionFieldBar M'` over $\overline{\mathbb Q}$ at which the $q$-expansion $j=$ `coeffEmb (AlgebraicClosure ℚ) jq` has nonnegative order, and with $R_0$-residue in the valuation subring of $s$, the image of $f$ in $F$ lies in $O^{\mathrm{ss}}(s)$, and for every $a\in A$ whose residue equals $s.\mathrm{evalAt}$ of that $R_0$-residue, the difference between the image of $f$ and $a$ lies in the maximal ideal of $O^{\mathrm{ss}}(s)$. The hypothesis `hSS_fix` requires each $O^{\mathrm{ss}}(s)$ to be invariant under preimage along `levelAutBar q M' ζ' γ` for all $\zeta'$ and all $\gamma\in\Gamma_0(M')$, and `hSS_tr` requires each $O^{\mathrm{ss}}(s)$ to contain an element $t$ such that $t-a$ is a unit of $O^{\mathrm{ss}}(s)$ for every $a\in A$.
--
--   Further, $R$ is a `RegularProlongation` of $A$ from $F$ to $\bar F_H=$ `xHFunctionFieldC κ (q^2*M') (levelH q M')` (valuation subring, surjective residue map with kernel the maximal ideal, compatibility with $A$ and its residue map, and the scaling property), with `hR` asserting $R.\mathrm{integers}=O^{\mathrm{Ig}}(\infty)$, and `hR₀O` asserting that $f$ lies in $R_0.\mathrm{integers}$ exactly when its image in $F$ lies in $O^{\mathrm{Ig}}(\infty)$. An element $\pi\in A$ with $\pi^{q^2-1}=q$ is given.
--
--   **Constants.** Let $k_0$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ and $\pi_0\in k_0\cap A$, and set $A\cap k_0=$ `A.comap (algebraMap k₀ (AlgebraicClosure ℚ))`. The hypotheses `hdvr`, `hunif`, `hhens`, `hres` require $A\cap k_0$ to be a discrete valuation ring with maximal ideal generated by $\pi_0$, henselian, with algebraically closed residue field; `hκ` requires every $a\in A$ to be congruent, modulo the maximal ideal of $A$, to an element of $k_0\cap A$; `hstab` requires every $\tau\in\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ preserving $A$ setwise to map $k_0$ into itself. An auxiliary prime $\ell\ge 3$ with $\ell\ne q$ and $\ell\nmid M'$ is given, together with $\zeta_0\in k_0$ a primitive $(q\ell)$-th root of unity and a tame element $\varpi_t\in k_0\cap A$ with $\varpi_t^{\,q^2-1}=q\cdot u$ for some unit $u$ of $A$. Finally a family $K:\iota\to$ intermediate fields of $\overline{\mathbb Q}/k_0$ is given, each finite-dimensional over $k_0$ (`hKfin`), with valuation subrings $A_n$ of $K_n$ satisfying $x\in A_n\iff x\in A$ (`hAn`).
--
--   **Conclusion.** Viewing $F$ as a $k_0$-algebra through $\overline{\mathbb Q}$, there exist an intermediate field $F_0$ of $F/k_0$, a finite set $N^{\mathrm{Ig}}$ of places of $\bar F_H$ over $\kappa$, subrings $S_{Q,n}\subseteq F$, ring homomorphisms $\varphi_{Q,n}:A_n[X]\to S_{Q,n}$ and $\chi_{Q,n}:S_{Q,n}\to\kappa$, and sets $D_{Q,n}$ of places of $F$ over $\overline{\mathbb Q}$, indexed by places $Q$ of $\bar F_H$ and by $n\in\iota$, such that the following hold.
--
--   (1) $\overline{\mathbb Q}\cdot F_0=F$: the join of `IntermediateField.adjoin k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) F))` with $F_0$ is $\top$.
--
--   (2) $F_0$ is stable under `levelAutBar q M' ζ' γ` for every $\zeta'\in$ `Idx q` and every $\gamma\in\Gamma_0(M')$.
--
--   (3) $N^{\mathrm{Ig}}$ and $W$ have the same cardinality.
--
--   (4) There is a ring homomorphism $j:\kappa(j,j_{M'})\to\bar F_H$ such that every $f\in R_0.\mathrm{integers}$ has its image in $F$ inside $R.\mathrm{integers}$ with $R$-residue $j(R_0.\mathrm{residue}\,f)$, and such that $Q\in N^{\mathrm{Ig}}$ holds exactly when there is $s\in W$ with: $g$ lies in the valuation subring of $s$ if and only if $j(g)$ lies in the valuation subring of $Q$.
--
--   (5) Every valuation subring $O\ne\top$ of $F$ containing the image of $\overline{\mathbb Q}$ is a principal ideal ring.
--
--   (6) For every place $Q$ of $\bar F_H$ with $Q\notin N^{\mathrm{Ig}}$, and every $n\in\iota$: the residue map $A_n\to\kappa$ is surjective; the image of each $a\in A_n$ in $F$ lies in $S_{Q,n}$; $\varphi_{Q,n}$ is formally smooth and formally unramified; $\varphi_{Q,n}(C\,a)$ is the image of $a$ in $F$ and $\chi_{Q,n}(\varphi_{Q,n}(C\,a))$ is the residue of $a$; $\chi_{Q,n}(\varphi_{Q,n}(X))=0$; for every $c\in A_n$ of residue $0$ there is a unique ring homomorphism $\chi:S_{Q,n}\to A_n$ with $\chi(\varphi_{Q,n}(C\,a))=a$ for all $a\in A_n$, with residue of $\chi(f)$ equal to $\chi_{Q,n}(f)$ for all $f$, and with $\chi(\varphi_{Q,n}(X))=c$; every $f\in S_{Q,n}$ lies in $R.\mathrm{integers}$ with $R$-residue in the valuation subring of $Q$, whose residue in $Q.\mathrm{ResidueField}$ is the image of $\chi_{Q,n}(f)$ under $\kappa\to Q.\mathrm{ResidueField}$; the $R$-residue of $\varphi_{Q,n}(X)$ has $Q$-order $1$; $D_{Q,n}$ consists exactly of the rational places $P$ of $F$ over $\overline{\mathbb Q}$ such that every $f\in S_{Q,n}$ lies in the valuation subring of $P$ with $P.\mathrm{evalAt}(f)\in A$, and such that $A$-valuation of $P.\mathrm{evalAt}(f)$ is $<1$ precisely when $\chi_{Q,n}(f)=0$; $\varphi_{Q,n}(X)\ne\varphi_{Q,n}(C\,c)$ for every $c\in A_n$; $S_{Q,n}$ is local with $f$ in its maximal ideal exactly when $\chi_{Q,n}(f)=0$; $S_{Q,n}$ is Noetherian and a unique factorisation monoid; $S_{Q,n}$ is contained in the join $L_n:=$ `IntermediateField.adjoin k₀` of the image of $K_n$ in $F$, joined with $F_0$, and every element of $L_n$ is a quotient $g/h$ with $g,h\in S_{Q,n}$, $h\ne 0$; $L_n$ is linearly disjoint from $\overline{\mathbb Q}$ over $K_n$ in the sense that for every $m$, every $c:\mathrm{Fin}\,m\to\overline{\mathbb Q}$ linearly independent over $K_n$ and every $a:\mathrm{Fin}\,m\to L_n$ with $\sum_i c_i a_i=0$ one has $a_i=0$ for all $i$; there is a generator $\varpi$ of the maximal ideal of $A_n$, $\varpi\ne 0$, such that $\varphi_{Q,n}(C\,\varpi)$ is prime in $S_{Q,n}$, such that an element of $L_n$ lies in $R.\mathrm{integers}$ exactly when it is $g/h$ with $g,h\in S_{Q,n}$ and $\varphi_{Q,n}(C\,\varpi)\nmid h$, and such that for every prime $p$ of $S_{Q,n}$ not associated to $\varphi_{Q,n}(C\,\varpi)$ and every $x\in S_{Q,n}$ there is a monic polynomial $r$ over $A_n$ with $p$ dividing the value at $x$ of $r$ pushed forward along $\varphi_{Q,n}\circ C$; every ring homomorphism $\chi:S_{Q,n}\to A_n$ fixing the coefficients and compatible with residues as above has kernel generated by $\varphi_{Q,n}(X)-\varphi_{Q,n}(C\,\chi(\varphi_{Q,n}(X)))$; and there is a finite subset $G\subseteq S_{Q,n}$ such that every $f\in S_{Q,n}$ is $g/h$ with $g,h$ in the subring generated by $G$ together with the image of $A_n$, and $h$ the image of a unit of $S_{Q,n}$.
--
--   Moreover, in the same clause, the subrings are monotone and cofinal along the tower: $K_n\le K_{n'}$ implies $S_{Q,n}\subseteq S_{Q,n'}$ and, conversely, $S_{Q,n'}$ is contained in the subring generated by $S_{Q,n}$ together with the image of $A_{n'}$; the images in $F$ of $\varphi_{Q,n}(X)$ and $\varphi_{Q,n'}(X)$ coincide for all $n,n'$; and $\chi_{Q,n'}$ restricted to $S_{Q,n}$ along the inclusion agrees with $\chi_{Q,n}$ whenever $K_n\le K_{n'}$.
--
--   (7) Distinct places $Q,Q'\notin N^{\mathrm{Ig}}$ have disjoint disc families: if $P\in D_{Q,n}\cap D_{Q',n}$ for some $n$, then $Q=Q'$.
--
--   (8) For every $\tau$ in the subgroup of $\mathrm{Aut}_{\overline{\mathbb Q}}(F)$ generated by the `levelAutBar q M' ζ' γ` with $\gamma\in\Gamma_0(M')$, and every proof that $\tau$ preserves $R.\mathrm{integers}$: the induced automorphism `R.resAut τ` of $\bar F_H$ over $\kappa$ carries $N^{\mathrm{Ig}}$ to itself, in the sense that $R.\mathrm{resAut}\,\tau\cdot Q\in N^{\mathrm{Ig}}\iff Q\in N^{\mathrm{Ig}}$, and for $Q\notin N^{\mathrm{Ig}}$ one has `smulDisc τ` $(D_{Q,n})=\{P:\tau^{-1}\cdot P\in D_{Q,n}\}=D_{R.\mathrm{resAut}\,\tau\cdot Q,\,n}$ for every $n$.
--
--   (9) For every $\tau$ in `A.inertiaSubgroupIn ℚ` and every $n$ such that $\tau$ preserves $K_n$, and every $Q\notin N^{\mathrm{Ig}}$: the coefficientwise action `arithmeticGalois (xHFunctionField (q^2*M') (levelH q M')) τ` preserves $S_{Q,n}$ in both directions, and $\chi_{Q,n}$ is invariant under it.
--
--   (10) For every $g$ in the subgroup generated by the `levelAutBar q M' ζ' γ` with $\gamma\in\Gamma_0(M')$ whose preimage of $O^{\mathrm{Ig}}(\infty)$ differs from $O^{\mathrm{Ig}}(\infty)$, and all $Q,Q'\notin N^{\mathrm{Ig}}$, all $n$ and all $P\in D_{Q,n}$, one has $g\cdot P\notin D_{Q',n}$.
--
--   (11) The discs avoid the supersingular points: for $Q\notin N^{\mathrm{Ig}}$, every $n$, every $P\in D_{Q,n}$ and every $s\in W$, it is not the case that both of the following hold — the image in $F$ of $j=$ `coeffEmb (AlgebraicClosure ℚ) jq` lies in the valuation subring of $P$ and for every $a\in A$ with residue $s.\mathrm{evalAt}(\mathrm{jGeomGen}\,\kappa\,M')$ the difference $P.\mathrm{evalAt}(j)-a$ lies in the maximal ideal of $A$; and the same two conditions for the image of `coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M' jq)` with `jNGeomGen κ M'` in place of `jGeomGen κ M'`.
--
--   (12) Conversely, every place $P$ of $F$ over $\overline{\mathbb Q}$ which for no $s\in W$ satisfies the reduction condition of `hSS_over` — namely that for every $f\in R_0.\mathrm{integers}$ of nonnegative order wherever $j$ has nonnegative order and with $R_0$-residue in the valuation subring of $s$, and every $a\in A$ whose residue is $s.\mathrm{evalAt}$ of that residue, $P.\mathrm{evalAt}$ of the image of $f$ differs from $a$ by an element of the maximal ideal of $A$ — admits $\gamma\in\Gamma_0(M')$ and $Q\notin N^{\mathrm{Ig}}$ with `levelAutBar q M' ζ γ` $\cdot P\in D_{Q,n}$ for every $n$.
--
--   (13) There is a place $P$ of $F$ over $\overline{\mathbb Q}$ whose valuation subring is `qIntegersBar (AlgebraicClosure ℚ) (fieldBar q M')`, the subring of elements of nonnegative Laurent order, together with a place $Q\notin N^{\mathrm{Ig}}$ such that $P\in D_{Q,n}$ for every $n$.
--
--   This assembles, at every finite layer $K_n$ of a tower of constant fields over $k_0$, the local data (a local subring $S_{Q,n}$ with a smooth presentation over $A_n[X]$, its residue character, and the associated residue disc) describing the Igusa components of the semistable model at $q$ of the modular curve of level $\Gamma_H(q^2M')$, away from the supersingular points indexed by $W$, together with the equivariance of this data under the level automorphisms and under inertia at $q$. It is used by [`ModularCurve.FullLevel.exists_igusaSmoothPointCharts_of_igusaGaussRing_allInertia`](thm.html#ModularCurve.FullLevel.exists_igusaSmoothPointCharts_of_igusaGaussRing_allInertia) to produce the smooth charts of the Igusa part of the model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_igusaTower_smoothPointData_of_stable.lean

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

theorem ModularCurve.FullLevel.exists_igusaTower_smoothPointData_of_stable
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
