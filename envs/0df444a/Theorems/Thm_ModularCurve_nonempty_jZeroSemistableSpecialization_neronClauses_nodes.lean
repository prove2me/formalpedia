-- Prove2me | Theorems.Thm_ModularCurve_nonempty_jZeroSemistableSpecialization_neronClauses_nodes
-- name    : ModularCurve.nonempty_jZeroSemistableSpecialization_neronClauses_nodes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/23310817-8a21-5d19-baf8-93a32fdc6449
-- title:
--   Semistable specialization datum for J₀(Nq) with Néron clauses
-- statement:
--   Let $N$ be a non-zero natural number and $q$ a prime not dividing $N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q$ in the sense that the image of $q$ lies in the non-units of $A$; write $\kappa =$ `IsLocalRing.ResidueField A`, and assume the set `ssPlaces q N κ` of supersingular places of the level-$N$ modular function field `modularFunctionFieldC κ N` over $\kappa$ is finite. With $J_0(M) =$ `JZero M` carrying the Hecke-algebra module structure `heckeModuleBar` for $M = Nq$ and $M = N$ (the Hecke algebra being `HeckeAlg` $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$), the assertion is that there is a `HeckeAlg`-module structure on $\operatorname{Pic}^0$ of `modularFunctionFieldC κ N` over $\kappa$ and a semistable specialization datum $D$ of type `JZeroSemistableSpecialization A N q hq` with the following nine further properties. (i) Its node set is exactly `nodePairsOfPlaces D.frob` applied to the finite set of supersingular places, i.e. the pairs $(w, D.\mathrm{frob}\cdot w)$ for $w$ supersingular. (ii) Inertia acts unipotently on prime-to-$q$ torsion: for $\sigma$ in `A.inertiaSubgroupIn ℚ` and $x \in J_0(Nq)$ annihilated by some positive integer prime to $q$, the element $\sigma\cdot x - x$ is inertia-invariant, is killed by the component map $D.\mathrm{comp}$, and its image under $D.\mathrm{sp}$ dies in $\operatorname{Pic}^0 \times \operatorname{Pic}^0$ under `toPic0Pair`. (iii) For $m$ coprime to $q$, every $m$-torsion element of the glued class group `GluedPic0` of $D.\mathrm{nodes}$ is $D.\mathrm{sp}(x)$ for some inertia-invariant $x$ with $m\cdot x = 0$ and $D.\mathrm{comp}(x) = 0$. (iv) For $m$ coprime to $q$, every $m$-torsion element of the component group `componentGroup D.width` is $D.\mathrm{comp}(x)$ for some inertia-invariant $x$ with $m\cdot x = 0$. (v) $D.\mathrm{comp}$ is surjective. (vi) and (vii) For $\sigma$ in the decomposition group of $A$ over $\mathbb{Q}$, the kernel of $D.\mathrm{comp}$, and inside it the locus where `toPic0Pair` of $D.\mathrm{sp}$ vanishes, are stable under $\sigma$ whenever $\sigma\cdot x$ is again inertia-invariant. (viii) On that locus the pair projection of $D.\mathrm{sp}$ is equivariant for the decomposition group through the level-$N$ specialization $D.\mathrm{spN}$: if `toPic0Pair` of $D.\mathrm{sp}(x)$ equals $(D.\mathrm{spN}(a), D.\mathrm{spN}(b))$ then the corresponding value at $\sigma\cdot x$ equals $(D.\mathrm{spN}(\sigma\cdot a), D.\mathrm{spN}(\sigma\cdot b))$. (ix) All widths $D.\mathrm{width}(s)$ are positive. (x) There is a `HeckeAlg`-module structure on `componentGroup D.width` making $D.\mathrm{comp}$ equivariant for every Hecke operator $T$ (whenever $T\cdot x$ is inertia-invariant), and such that for every maximal ideal $\mathfrak{m}$ of `HeckeAlg` with vanishing $\mathfrak{m}$-torsion in the component group, every $x$ in the $\mathfrak{m}$-torsion of $J_0(Nq)$ that is annihilated by a positive integer prime to $q$, is inertia-invariant, and satisfies $D.\mathrm{comp}(x) = 0$ and vanishing of `toPic0Pair` of $D.\mathrm{sp}(x)$, lies in `toricMonodromyPart q (A.inertiaSubgroupIn ℚ)`, the Hecke-submodule spanned by the elements $\sigma\cdot y - y$ with $\sigma$ in inertia and $y$ killed by a positive integer coprime to $q$.
--
--   This packages the arithmetic input coming from the Néron model of $J_0(Nq)$ over $\mathbb{Z}_{(q)}$ and the Deligne–Rapoport description of the fibre at $q$: the glued class group and component group of the reduction, with nodes indexed by supersingular points, unipotence of inertia on prime-to-$q$ torsion, divisibility of specialization on prime-to-$q$ torsion, and Galois and Hecke equivariance. It is cited by [`ModularCurve.exists_jZeroSemistableSpecialization_ssPlaces_monodromy`](thm.html#ModularCurve.exists_jZeroSemistableSpecialization_ssPlaces_monodromy), the form of the statement used in the level-lowering step at the auxiliary prime $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_nonempty_jZeroSemistableSpecialization_neronClauses_nodes.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_SupersingularNodePlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

theorem ModularCurve.nonempty_jZeroSemistableSpecialization_neronClauses_nodes (N q : ℕ) [NeZero N] (hq : q.Prime)
    (hqN : ¬ q ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    [DecidableEq (IsLocalRing.ResidueField A)]
    [Fintype ↥(ssPlaces q N (IsLocalRing.ResidueField A))] :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    letI := ModularCurve.heckeModuleBar (N * q)
    letI := ModularCurve.heckeModuleBar N
    letI := ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∃ _ : Module ModularCurve.HeckeAlg
        (AlgebraicCurve.Pic0 (IsLocalRing.ResidueField ↥A)
          ↥(ModularCurve.modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)),
      ∃ D : ModularCurve.JZeroSemistableSpecialization A N q hq,
        D.nodes = nodePairsOfPlaces D.frob
          (ssPlaces q N (IsLocalRing.ResidueField A)).toFinset ∧
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
