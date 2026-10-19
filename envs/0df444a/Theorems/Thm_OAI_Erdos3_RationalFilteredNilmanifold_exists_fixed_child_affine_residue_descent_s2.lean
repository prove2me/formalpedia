-- Prove2me | Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_fixed_child_affine_residue_descent_s2
-- name    : OAI.Erdos3.RationalFilteredNilmanifold.exists_fixed_child_affine_residue_descent_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T03:59:20.050742+00:00
-- url     : https://prove2.me/theorems/7b4664c4-91c9-453f-a1c2-78a471aee689
-- title:
--   Existence of a fixed child polynomial orbit with affine residue descent on a lowered cover of a refiltered quotient nilmanifold
-- statement:
--   Let $s$ and $a$ be natural numbers. Then there is a natural number $C \ge 2$ with the following property.
--
--   Let $\sigma$ be a finite type with decidable equality, let $L$ be a Lie algebra over $\mathbb{Q}$ such that $\mathbb{R} \otimes_{\mathbb{Q}} L$ carries a Hausdorff topology making it a topological additive group with continuous real scalar multiplication, let $d$ be a natural number, and let $D$ be a `RationalFilteredNilmanifold L (s + 1) d` (OpenAI's structure: a nilpotent Lie filtration `D.filtration` of $L$ of step $s+1$, a $\mathbb{Q}$-basis `D.basis` of $L$ indexed by $\operatorname{Fin} d$, bases of the layers, and a lattice subgroup `D.lattice` of the associated group, together with further data). Let $p \ge 0$ be real with `D.GeometryComplexityLE p` (OpenAI's predicate: $d \le p$, the grid parameter of $D$ is at most $e^p$, and the rational log-heights of the structure constants and of the layer-basis coordinates are at most $p$) and $|\sigma| \le p$. Let $q$ be a natural number with $0 < q \le e^p$.
--
--   Then there exists a natural number $P > 0$ with $P \le e^{(p+2)^C}$ such that the following holds for every Lie subalgebra $W$ of the associated graded Lie algebra of `D.filtration`, all natural numbers $e, n$, and all data as follows:
--
--   - $E$, a `RationalFilteredNilmanifold H (s + 1) e`, where $H$ = `D.filtration.gradedRefiltrationSubalgebra W` is OpenAI's Lie subalgebra of $L$ obtained by refiltering along $W$, with `E.filtration` $=$ `D.filtration.gradedRefiltration W` (OpenAI's refiltration of $H$);
--   - $Q$, a `RationalFilteredNilmanifold N s n`, where $N = H / \texttt{E.filtration.layerIdeal (s + 1)}$ is the quotient of $H$ by the ideal given by layer $s+1$ of `E.filtration`, with `Q.filtration` $=$ `E.filtration.quotientTop` (the induced filtration of step $s$ on the quotient);
--   - $b$, an element of the group of `D.filtration.realification.adaptedPolynomialFiltration (fun _ => 1)` (OpenAI's group of adapted polynomial maps in the variables $\sigma$, with all variables of weight $1$, into the realification of $L$), such that for every multi-index $\alpha$ the coefficient of $\alpha$ in the coordinate polynomial `b.coord` lies in `D.filtration.realGradedRefiltrationLayer W |α|` (the real base change of layer $|\alpha|$ of the refiltration, where $|\alpha|$ is the total degree), and the constant coefficient of `b.coord` is $0$;
--   - a real number $\mathrm{cost} \ge 0$ such that `SingleRefilteredRecoveryFamily D W E Q p q C cost` holds (OpenAI's predicate asserting the existence of a characteristic finite-index sublattice, a lowered cover, and Lipschitz recovery of invariant test functions with complexity bounded by cost).
--
--   For these, with $N$ given the module topology on $\mathbb{R} \otimes_{\mathbb{Q}} N$ and $T$ = `Q.raiseStep` (the nilmanifold $Q$ regarded as having step $s+1$), the conclusion is: there is a subgroup $\Lambda$ of the group of `T.filtration` with $\Lambda \le$ `T.lattice`, such that $\Lambda$, as a subgroup of `T.lattice`, is characteristic, normal and of finite index, with index $[\texttt{T.lattice} : \Lambda] \le e^{\mathrm{cost}}$; and there are a natural number $B > 0$ and inclusions
--   $$B\,\mathbb{Z}^n \subseteq \texttt{bchSubgroupCoordinates Q.basis } \Lambda \subseteq \tfrac{1}{B}\mathbb{Z}^n$$
--   (`scaledIntegerGrid B` and `denominatorGrid B`; the middle set is the set of rational coordinate vectors, in the basis `Q.basis`, of elements of $\Lambda$), such that, writing $V$ for `Q.loweredCover (Nat.le_succ s) Λ B hB hin hout` (OpenAI's nilmanifold with the filtration of $Q$ and lattice built from $\Lambda$), one has `V.filtration` $=$ `Q.filtration`, `V.lattice` $\le$ `Q.lattice`, `V.GeometryComplexityLE cost`, and there exists a polynomial orbit `child` of `V.filtration.realification` with all variables of weight $1$ (`PolynomialOrbit (fun _ => 1)`) whose logarithm `child.log` has total degree at most $s$ and such that `FixedAffineResidueDescent D W V b child p q P hP C a (cost + 4)` holds (OpenAI's predicate: for every integer scale and integer shift vector, the affine reparametrizations of $b$ and of `child` satisfy OpenAI's `FixedResidueDescent` with these parameters).
--
--   Lean: `OAI.Erdos3.RationalFilteredNilmanifold.exists_fixed_child_affine_residue_descent_s2`, which states OpenAI's `OAI.Erdos3.RationalFilteredNilmanifold.exists_fixed_child_affine_residue_descent` (in `lean/OAI/Combinatorics/Progressions/Lattices/RetainedAffineResidueEpoch.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B192` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/RetainedAffineResidueEpoch.lean (declaration OAI.Erdos3.RationalFilteredNilmanifold.exists_fixed_child_affine_residue_descent)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B192

section

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

theorem exists_fixed_child_affine_residue_descent_s2 (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d),
      ∀ p : ℝ, 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ (P : ℕ) (hP : 0 < P), (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
      ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) {e n : ℕ}
        (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
        (Q : RationalFilteredNilmanifold
          ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
        (_hEF : E.filtration = D.filtration.gradedRefiltration W)
        (_hQF : Q.filtration = E.filtration.quotientTop)
        (b : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) →
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 →
        ∀ cost : ℝ, 0 ≤ cost → SingleRefilteredRecoveryFamily D W E Q p q C cost →
        let H := D.filtration.gradedRefiltrationSubalgebra W
        let N := H ⧸ E.filtration.layerIdeal (s + 1)
        let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
        let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
        let := realification_moduleTopology_t2 Q.basis
        let T := Q.raiseStep (Nat.le_succ s)
        ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
          (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
          (Λ.subgroupOf T.lattice).FiniteIndex ∧ (Λ.relIndex T.lattice : ℝ) ≤ Real.exp cost ∧
          ∃ (B : ℕ) (hB : 0 < B)
            (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates Q.basis Λ)
            (hout : bchSubgroupCoordinates Q.basis Λ ⊆ denominatorGrid B),
            let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
            V.filtration = Q.filtration ∧ V.lattice ≤ Q.lattice ∧ V.GeometryComplexityLE cost ∧
            ∃ child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
              DegreeLE (fun _ => 1) s child.log ∧
              FixedAffineResidueDescent D W V b child p q P hP C a (cost + 4) := by
  sorry

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end
