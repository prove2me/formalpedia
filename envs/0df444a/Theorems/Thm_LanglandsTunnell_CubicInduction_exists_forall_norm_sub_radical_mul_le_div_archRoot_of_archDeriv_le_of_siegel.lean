-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel
-- name    : LanglandsTunnell.CubicInduction.exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/afb02351-9211-5527-a83d-58022e08f21d
-- title:
--   Unipotent displacement on a Siegel set in GL₃(A_ℚ)
-- statement:
--   Let $c, C, M'$ be real numbers with $0 < c$ and $0 \le M'$, and let $Dc$ be a compact set of real $3\times 3$ arrays all of which have nonzero determinant. Then there are a compact set $Dc'$ of arrays of nonzero determinant with $Dc \subseteq Dc'$, and a real $\kappa \ge 0$, with the following property. Let $F : \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ satisfy `IsArchSmooth3`, i.e. for every $g$ the map $e \mapsto F(g \cdot \mathtt{archRealLift3}\,e)$ is $C^\infty$ on the set of invertible real arrays, where $\mathtt{archRealLift3}\,e$ is the adelic matrix with archimedean entries $e$ and trivial finite part (or $1$ if that matrix is not invertible). Let $n, t, k \in \mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$ be such that: at every height-one prime $p$ of $\mathbb{Z}$ the components of $n$ and of $t$ are the identity and that of $k$ lies in `localMaximalCompact3`, the subgroup of matrices over $\mathbb{Q}_p$ all of whose entries, and all of whose inverse's entries, have valuation $\le 1$; and at every infinite place $w$ of $\mathbb{Q}$ the component of $n$ has diagonal entries $1$, vanishing entries below the diagonal and all entries of norm $\le C$, the component of $t$ is diagonal with $c \le \mathtt{archRoot}_1\,t$ and $c \le \mathtt{archRoot}_2\,t$, and the component of $k$ is orthogonal. Let $B$ be a real number such that $\|\mathtt{archDeriv}\,i\,j\,F(ntk \cdot \mathtt{archRealLift3}\,e')\| \le B$ for all $e' \in Dc'$ and all $i,j$, where $\mathtt{archDeriv}\,i\,j\,F(g)$ is the derivative at $s = 0$ of $s \mapsto F(g \cdot \mathtt{archRealLift3}(1 + sE_{ij}))$. Then for every $e \in Dc$, all adeles $x, y$ whose archimedean coordinates have norm $\le M'$ at every infinite place, and every infinite place $w$, writing $g = ntk$ and $L = \mathtt{archRealLift3}\,e$, one has $\|F(gL) - F(u\,g\,L)\| \le \kappa B / \mathtt{archRoot}_2\,t$ for $u$ the unipotent matrix with $(1,3)$ entry $x_\infty$ and $(2,3)$ entry $y_\infty$ (the radical of the parabolic of type $(2,1)$), and $\|F(gL) - F(u'gL)\| \le \kappa B / \mathtt{archRoot}_1\,t$ for $u'$ the unipotent matrix with $(1,2)$ entry $x_\infty$ and $(1,3)$ entry $y_\infty$; here $x_\infty, y_\infty$ are taken with trivial finite part, and $\mathtt{archRoot}_1, \mathtt{archRoot}_2$ are the simple-root quantities attached to $t$ at $w$.
--
--   This is the archimedean displacement estimate on a Siegel set in $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$: translating on the left by a bounded element of the unipotent radical of one of the two maximal parabolics moves a function smooth at the infinite place by at most a constant times a bound on its first right-invariant derivatives, divided by the opposite simple root of the diagonal part. The constants $\kappa$ and the enlarged compact set $Dc'$ are uniform in $F$, which is what allows it to be applied to all derivative words at once in the rapid-decay bound `norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

theorem LanglandsTunnell.CubicInduction.exists_forall_norm_sub_radical_mul_le_div_archRoot_of_archDeriv_le_of_siegel
    (c C M' : ℝ) (hc0 : 0 < c) (hM' : 0 ≤ M')
    (Dc : Set (Fin 3 → Fin 3 → ℝ)) (hDc : IsCompact Dc) (hDcU : Dc ⊆ {e | (Matrix.of e).det ≠ 0}) :
    ∃ Dc' : Set (Fin 3 → Fin 3 → ℝ), IsCompact Dc' ∧ Dc' ⊆ {e | (Matrix.of e).det ≠ 0} ∧ Dc ⊆ Dc' ∧
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, WhittakerBlock.IsArchSmooth3 F →
      ∀ n t k : AdelicGL 3 (𝓞 ℚ) ℚ,
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) →
        (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) →
        (∀ w : InfinitePlace ℚ,
          (∀ i j : Fin 3,
            (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
            (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
          (∀ i j : Fin 3, i ≠ j →
            (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
          c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
          (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
              (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1) →
        ∀ B : ℝ, (∀ e' ∈ Dc', ∀ i j : Fin 3,
            ‖WhittakerBlock.archDeriv i j F (n * t * k * WhittakerBlock.archRealLift3 e')‖ ≤ B) →
        ∀ e ∈ Dc, ∀ x y : AdeleRing (𝓞 ℚ) ℚ,
          (∀ w : InfinitePlace ℚ, ‖x.1 w‖ ≤ M') → (∀ w : InfinitePlace ℚ, ‖y.1 w‖ ≤ M') →
          ∀ w : InfinitePlace ℚ,
            ‖F (n * t * k * WhittakerBlock.archRealLift3 e) -
                F (radicalP21 (![(x.1, 0), (y.1, 0)] : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) * (n * t * k) *
                  WhittakerBlock.archRealLift3 e)‖ ≤ κ * B / archRoot₂ ℚ w t ∧
            ‖F (n * t * k * WhittakerBlock.archRealLift3 e) -
                F (radicalP12 (![(x.1, 0), (y.1, 0)] : Fin 2 → AdeleRing (𝓞 ℚ) ℚ) * (n * t * k) *
                  WhittakerBlock.archRealLift3 e)‖ ≤ κ * B / archRoot₁ ℚ w t := by sorry
