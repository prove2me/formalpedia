-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_admissibleChain_filtAlpha_eq
-- name    : ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_admissibleChain_filtAlpha_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/582f6688-6ff9-5cbf-952a-32abb2ef4c15
-- title:
--   Admissible chain from a primary Néron torsion flag
-- statement:
--   Let $p$ and $q$ be primes with $q \neq 2$, assume that all the Hecke operators `heckeOperatorBar p` commute with one another (the hypothesis `HeckeOperatorsCommuteBar p`, which is what makes `heckeModuleBar p` the Hecke-algebra module structure on $J_0 =$ `JZero p`, the degree-zero divisor class group $\mathrm{Pic}^0$ of `modularFunctionFieldBar p` over $\overline{\mathbb{Q}}$), and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$. Let $C$ be a localised Néron primary-torsion core `JZeroNeronPrimaryTorsionCore p q A hA`, let $m : \mathbb{N}$, and let `flag` be a flag `JZeroNeronPrimaryTorsionFlag p q A hA C m` of length `flag.n`: a chain of finite-type flat Hopf-algebra quotients $G_i$ of $C.H\,m$, a compatible chain of subsheaves $F_i \hookrightarrow C.\mathcal{J}\,m$ on the small fppf site of $\operatorname{Spec}\mathbb{Z}$ realising them on sections, an increasing Galois-stable filtration `flag.genericStep` of the subgroup $M :=$ `eisensteinPrimaryTorsionBar p q m` of $J_0$ (the intersection of the kernel of multiplication by $q^m$ with the union of the $(\mathfrak{p}^k)$-torsion for the powers of `eisensteinMaximalIdeal p q`), and a labelling `flag.kind` of its layers by `const` or `mult`. Let $\Phi$ be an `OpenAction` on $M$, i.e. a homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathrm{Aut}(M)$ with open kernel, and assume $\Phi$ induces the natural Galois action, $(\Phi.\varphi\,\sigma\,x : J_0) = \sigma \cdot x$ for all $\sigma$ and all $x \in M$. Then there exists an admissible chain $c :$ `AdmissibleChain q Φ`, that is a filtration $\bot = c_0 \le c_1 \le \dots \le c_n = \top$ of $M$ by additive subgroups together with tags in `Bool`, each successive quotient having exactly $q$ elements and each step being $\Phi$-trivial when tagged `true` and $q$-cyclotomic otherwise, such that `filtAlpha c`, the number of steps tagged `true`, equals the number of indices $i$ with `flag.kind i = JZeroFlagLayerKind.const`, and `filtLength c = flag.n`.
--
--   This converts the Jordan–Hölder data of the localised Néron model of the $\mathfrak{p}$-primary $q^m$-torsion of $J_0(p)$ into the group-theoretic input used on the Galois side: an admissible chain whose trivial steps correspond exactly to the constant ($\mathbb{Z}/q$) layers and whose cyclotomic steps correspond to the multiplicative ($\mu_q$) layers, in the style of Mazur's analysis of the Eisenstein ideal. It is used by [`ModularCurve.jZeroNeronTorsionSheaf_device_v5`](thm.html#ModularCurve.jZeroNeronTorsionSheaf_device_v5).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_admissibleChain_filtAlpha_eq.lean

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag
import Definitions.Def_MazurAdmissible_GaloisModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve MazurAdmissible AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring

theorem ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_admissibleChain_filtAlpha_eq (p : ℕ) [Fact p.Prime]
    (hcomm : HeckeOperatorsCommuteBar p) (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m)
    (Φ : letI := heckeModuleBar p
      OpenAction ↥(eisensteinPrimaryTorsionBar p q m))
    (hΦ : letI := heckeModuleBar p
      ∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))
        (x : ↥(eisensteinPrimaryTorsionBar p q m)),
        (Φ.φ σ x : JZero p) = σ • (x : JZero p)) :
    letI := heckeModuleBar p
    ∃ c : AdmissibleChain q Φ,
      filtAlpha c = (Finset.univ.filter (fun i => flag.kind i = JZeroFlagLayerKind.const)).card ∧
      filtLength c = flag.n := by sorry
