-- Prove2me | Theorems.Thm_ModularCurve_nonempty_jZeroSemistableSpecialization_neronClauses
-- name    : ModularCurve.nonempty_jZeroSemistableSpecialization_neronClauses
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/27e65756-4596-5ed3-b3ac-4388c44a2fd9
-- title:
--   Semistable specialisation datum for J₀(Nq) with Néron clauses
-- statement:
--   Let $N$ be a nonzero natural number, $q$ a prime with $q \nmid N$, and $A$ a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a nonunit of $A$; write $\kappa$ for the residue field of $A$ and $F = \mathtt{modularFunctionFieldC}\ \kappa\ N$ for the level-$N$ modular function field over $\kappa$, and equip $\mathtt{JZero}\,(N q)$ and $\mathtt{JZero}\,N$ — the degree-zero divisor class groups of the base-changed modular function fields over $\overline{\mathbb{Q}}$ — with the Hecke-algebra structures [`ModularCurve.heckeModuleBar`](def/ModularCurve_HeckeModule.html#L82), the Hecke algebra being $\mathbb{Z}[X_\ell : \ell \text{ prime}]$. Then there exist a Hecke-algebra module structure on $\mathrm{Pic}^0(\kappa, F)$ and a datum $D$ of type [`ModularCurve.JZeroSemistableSpecialization A N q hq`](def/ModularCurve_JZeroSemistableSpecialization.html#L94) (nodes with rational residue fields, a $q$-power semilinear Frobenius stabilising them, widths, a component map $\mathrm{comp}$ on the inertia invariants $H = \{x \in \mathtt{JZero}(Nq) : \sigma x = x \text{ for all } \sigma \in I_A\}$ with values in the component group $\mathrm{Coker}$ of the Gram map attached to the widths, a specialisation map $\mathrm{sp}$ into the glued class group $\mathtt{GluedPic0}$, a level-$N$ map $\mathrm{spN}$, and the laws of that structure) satisfying the following further clauses, where $I_A$ denotes the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $A$, $\nu = \mathtt{toPic0Pair}$ is the projection of $\mathtt{GluedPic0}$ onto $\mathrm{Pic}^0 \times \mathrm{Pic}^0$, and the toric locus means the common kernel of $\mathrm{comp}$ and $\nu \circ \mathrm{sp}$: (i) for $\sigma \in I_A$ and $x \in \mathtt{JZero}(Nq)$ killed by some positive integer prime to $q$, the element $\sigma x - x$ lies in $H$ and in the toric locus; (ii) for every $m$ coprime to $q$, every $g \in \mathtt{GluedPic0}$ with $m g = 0$ is $\mathrm{sp}\,x$ for some $x \in H$ with $m x = 0$ and $\mathrm{comp}\,x = 0$; (iii) likewise every $m$-torsion element of the component group is $\mathrm{comp}\,x$ for some $m$-torsion $x \in H$; (iv) $\mathrm{comp}$ is surjective; (v)–(vii) for $\sigma$ in the decomposition group of $A$ and $x \in H$ with $\sigma x \in H$: $\mathrm{comp}\,x = 0$ implies $\mathrm{comp}(\sigma x) = 0$, and then $\nu(\mathrm{sp}\,x) = 0$ implies $\nu(\mathrm{sp}(\sigma x)) = 0$, and $\nu(\mathrm{sp}\,x) = (\mathrm{spN}\,a, \mathrm{spN}\,b)$ implies $\nu(\mathrm{sp}(\sigma x)) = (\mathrm{spN}(\sigma a), \mathrm{spN}(\sigma b))$; (viii) all widths are positive; (ix) there is a Hecke-algebra module structure on the component group making $\mathrm{comp}$ Hecke-equivariant (whenever $T x \in H$) and such that for every maximal ideal $\mathfrak{m}$ of the Hecke algebra with vanishing $\mathfrak{m}$-torsion in the component group, every $\mathfrak{m}$-torsion element $x$ of $\mathtt{JZero}(Nq)$ that is killed by a positive integer prime to $q$, lies in $H$ and lies in the toric locus belongs to $\mathtt{toricMonodromyPart}\ q\ I_A$, the Hecke-span of the elements $\sigma y - y$ with $\sigma \in I_A$ and $y$ killed by a positive integer coprime to $q$.
--
--   This packages the arithmetic input supplied by the Néron model of $J_0(Nq)$ over $\mathbb{Z}_{(q)}$ and the Deligne–Rapoport description of the fibre at $q$: Grothendieck's unipotence of inertia on prime-to-$q$ torsion, divisibility of the specialisation and component maps on torsion prime to $q$, surjectivity onto the component group, equivariance under the decomposition group, positivity of the crossing widths, and the monodromy statement at maximal ideals of the Hecke algebra with trivial component-group torsion. It is the existence statement used in the level-lowering step, and is invoked by the newform results on eigenplanes and torsion lines in the Tate module of $J_0(Nq)$ and by the statement locating monodromy in the toric locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_nonempty_jZeroSemistableSpecialization_neronClauses.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

theorem ModularCurve.nonempty_jZeroSemistableSpecialization_neronClauses (N q : ℕ) [NeZero N] (hq : q.Prime)
    (hqN : ¬ q ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    letI := ModularCurve.heckeModuleBar (N * q)
    letI := ModularCurve.heckeModuleBar N
    letI := ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∃ _ : Module ModularCurve.HeckeAlg
        (AlgebraicCurve.Pic0 (IsLocalRing.ResidueField ↥A)
          ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)),
      ∃ D : ModularCurve.JZeroSemistableSpecialization A N q hq,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : ModularCurve.JZero (N * q),
          ModularCurve.PrimeToTorsion q x →
            ∃ h : σ • x - x ∈ ModularCurve.inertiaInvariants A (N * q),
              D.comp ⟨σ • x - x, h⟩ = 0 ∧
                AlgebraicCurve.GluedPic0.toPic0Pair D.nodes (D.sp ⟨σ • x - x, h⟩) = 0) ∧
        (∀ m : ℕ, m.Coprime q →
          ∀ g : AlgebraicCurve.GluedPic0 (IsLocalRing.ResidueField ↥A)
              ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N) D.nodes,
            (m : ℤ) • g = 0 →
              ∃ x : ↥(ModularCurve.inertiaInvariants A (N * q)),
                (m : ℤ) • (x : ModularCurve.JZero (N * q)) = 0 ∧ D.comp x = 0 ∧ D.sp x = g) ∧
        (∀ m : ℕ, m.Coprime q →
          ∀ φ : ModularCurve.componentGroup D.width, (m : ℤ) • φ = 0 →
            ∃ x : ↥(ModularCurve.inertiaInvariants A (N * q)),
              (m : ℤ) • (x : ModularCurve.JZero (N * q)) = 0 ∧ D.comp x = φ) ∧
        Function.Surjective D.comp ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ →
          ∀ (x : ↥(ModularCurve.inertiaInvariants A (N * q)))
            (hx : σ • (x : ModularCurve.JZero (N * q)) ∈ ModularCurve.inertiaInvariants A (N * q)),
            D.comp x = 0 → D.comp ⟨σ • (x : ModularCurve.JZero (N * q)), hx⟩ = 0) ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ →
          ∀ (x : ↥(ModularCurve.inertiaInvariants A (N * q)))
            (hx : σ • (x : ModularCurve.JZero (N * q)) ∈ ModularCurve.inertiaInvariants A (N * q)),
            D.comp x = 0 → AlgebraicCurve.GluedPic0.toPic0Pair D.nodes (D.sp x) = 0 →
              AlgebraicCurve.GluedPic0.toPic0Pair D.nodes
                (D.sp ⟨σ • (x : ModularCurve.JZero (N * q)), hx⟩) = 0) ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.decompositionSubgroup ℚ →
          ∀ (x : ↥(ModularCurve.inertiaInvariants A (N * q)))
            (hx : σ • (x : ModularCurve.JZero (N * q)) ∈ ModularCurve.inertiaInvariants A (N * q)),
            D.comp x = 0 → ∀ a b : ModularCurve.JZero N,
              AlgebraicCurve.GluedPic0.toPic0Pair D.nodes (D.sp x) = (D.spN a, D.spN b) →
                AlgebraicCurve.GluedPic0.toPic0Pair D.nodes
                    (D.sp ⟨σ • (x : ModularCurve.JZero (N * q)), hx⟩)
                  = (D.spN (σ • a), D.spN (σ • b))) ∧
        (∀ s : ↥D.nodes, 0 < D.width s) ∧
        (∃ _ : Module ModularCurve.HeckeAlg (ModularCurve.componentGroup D.width),
          (∀ (T : ModularCurve.HeckeAlg) (x : ↥(ModularCurve.inertiaInvariants A (N * q)))
            (hx : T • (x : ModularCurve.JZero (N * q)) ∈ ModularCurve.inertiaInvariants A (N * q)),
            D.comp ⟨T • (x : ModularCurve.JZero (N * q)), hx⟩ = T • D.comp x) ∧
          (∀ 𝔪 : Ideal ModularCurve.HeckeAlg, 𝔪.IsMaximal →
            ModularCurve.heckeTorsion (ModularCurve.componentGroup D.width) 𝔪 = ⊥ →
              ∀ x ∈ ModularCurve.heckeTorsion (ModularCurve.JZero (N * q)) 𝔪,
                ModularCurve.PrimeToTorsion q x →
                  ∀ h : x ∈ ModularCurve.inertiaInvariants A (N * q), D.comp ⟨x, h⟩ = 0 →
                    AlgebraicCurve.GluedPic0.toPic0Pair D.nodes (D.sp ⟨x, h⟩) = 0 →
                      x ∈ ModularCurve.toricMonodromyPart (J := ModularCurve.JZero (N * q)) q
                        (A.inertiaSubgroupIn ℚ))) := by sorry
