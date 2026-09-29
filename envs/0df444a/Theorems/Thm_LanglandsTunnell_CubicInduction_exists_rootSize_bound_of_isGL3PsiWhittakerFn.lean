-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_rootSize_bound_of_isGL3PsiWhittakerFn
-- name    : LanglandsTunnell.CubicInduction.exists_rootSize_bound_of_isGL3PsiWhittakerFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/247d23c8-e38d-5481-9fa6-d3aebf86a8e2
-- title:
--   Root-size support and growth bound for local GL₃ Whittaker functions
-- statement:
--   Let $v$ be a nonzero prime of $\mathcal{O}_{\mathbb Q}$ and let $\psi$ be an additive character of the adele ring of $\mathbb Q$ whose local component $\psi_v$ — the composite of $\psi$ with the additive map sending $\mathbb Q_v$ into the adeles by placing it in the $v$-th coordinate of the finite part — is non-trivial. Let $W \colon \mathrm{GL}_3(\mathbb Q_v) \to \mathbb C$ satisfy: the Whittaker law $W(u(x,y,z)g) = \psi_v(x+y)\,W(g)$ for all $x,y,z \in \mathbb Q_v$ and all $g$, where $u(x,y,z)$ is the upper triangular unipotent matrix with entries $x$, $y$, $z$ above the diagonal; right invariance under some open subgroup $U_v$; and the admissibility condition that for every open subgroup $U_v$ there is a finite set $B$ of functions such that every element of the $\mathbb C$-span of the right translates $h \mapsto W(hg)$ of $W$ which is right $U_v$-invariant lies in the span of $B$. Assume moreover $W(\mathrm{diag}(z,z,z)\,g) = \chi(z)W(g)$ for a homomorphism $\chi \colon \mathbb Q_v^\times \to \mathbb C^\times$ with $\|\chi(z)\| = 1$ throughout. For $h \in \mathrm{GL}_3(\mathbb Q_v)$ put $d(h) = \|\det h\|$, let $r(h)$ be the maximum of the norms of the three entries of the last row of $h$, and let $m(h)$ be the maximum of the norms of the three $2 \times 2$ minors $h_{1j}h_{2j'} - h_{1j'}h_{2j}$ of its last two rows. Then there exist $B \in \mathbb R$, $t \in \mathbb N$ and $C \in \mathbb R$ such that for every $h$: if not both $d(h)r(h)/m(h)^2 \le B$ and $m(h)/r(h)^2 \le B$ then $W(h) = 0$; and if both hold then $\|W(h)\| \le C \big/ \big((d(h)r(h)/m(h)^2)\,(m(h)/r(h)^2)\big)^{t}$.
--
--   This is the local bound expressing that a smooth admissible Whittaker function on $\mathrm{GL}_3$ over a completion of $\mathbb Q$, with unitary central character, is supported where the two root sizes $d r/m^2$ and $m/r^2$ are bounded and decays there at most polynomially in those quantities. It is the majorant used to control the convergence and functional equation of the local zeta integrals attached to such Whittaker functions, and is cited by the statements about `localZeta30` and `localZetaDual31` and by the vanishing of `jacquetWhittaker3` for large root size.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_rootSize_bound_of_isGL3PsiWhittakerFn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_rootSize_bound_of_isGL3PsiWhittakerFn
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) (hψv : psiLoc ψ v ≠ 1)
    (W : LocalGL3 v → ℂ) (hW : IsGL3PsiWhittakerFn (psiLoc ψ v) W)
    (hsm : ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : LocalGL3 v, W (g * k) = W g)
    (hadm : ∀ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) →
      ∃ B : Finset (LocalGL3 v → ℂ), ∀ F ∈ gl3CyclicSubspace W,
        (∀ k ∈ Uv, ∀ g : LocalGL3 v, F (g * k) = F g) → F ∈ Submodule.span ℂ (B : Set (LocalGL3 v → ℂ)))
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (hχ : ∀ z : (v.adicCompletion ℚ)ˣ, ‖((χ z : ℂˣ) : ℂ)‖ = 1)
    (hcen : ∀ (z : (v.adicCompletion ℚ)ˣ) (g : LocalGL3 v),
      W (Matrix.GeneralLinearGroup.scalar (Fin 3) z * g) = ((χ z : ℂˣ) : ℂ) * W g) :
    ∃ (B : ℝ) (t : ℕ) (C : ℝ), ∀ h : LocalGL3 v,
      (¬ (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B) → W h = 0) ∧
      (detSize h * lastRowSup h / minorSup h ^ 2 ≤ B ∧ minorSup h / lastRowSup h ^ 2 ≤ B →
        ‖W h‖ ≤ C / ((detSize h * lastRowSup h / minorSup h ^ 2) * (minorSup h / lastRowSup h ^ 2)) ^ t) := by sorry
