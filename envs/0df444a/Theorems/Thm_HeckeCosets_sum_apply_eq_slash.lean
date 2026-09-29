-- Prove2me | Theorems.Thm_HeckeCosets_sum_apply_eq_slash
-- name    : HeckeCosets.sum_apply_eq_slash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/2dd01ce4-5fb8-543c-be1c-53a74cc8174d
-- title:
--   Adelic Hecke coset sum at p ∤ N in classical terms
-- statement:
--   Let $N \ge 1$, let $\varepsilon$ be a Dirichlet character modulo $N$ with values in $\mathbb{C}$, and let $F$ be a cusp form of weight $2$ on $\Gamma_1(N)$ satisfying [`CuspForm.HasNebentypus`](def/CuspForm_PrimitiveFormGamma1.html#L13) for $\varepsilon$, i.e. $F(\gamma\tau)=\varepsilon(d)\,(c\tau+d)^{2}F(\tau)$ for every $\gamma\in\mathrm{SL}_2(\mathbb{Z})$ lying in $\Gamma_0(N)$, with $c=\gamma_{10}$, $d=\gamma_{11}$, and every $\tau$ in the upper half-plane. Let $\Psi$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $\mathbb{Q}$ which is an adelic lift of $F$ in the sense of [`CuspForm.IsAdelicLiftOfGamma1`](def/CuspForm_AdelicLiftGamma1.html#L14): it is invariant under left translation by the image of $\mathrm{GL}_2(\mathbb{Q})$ under [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15), invariant under right translation by the image under [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145) of the level-one subgroup [`NumberField.AdelicLevel.finiteLevelOne`](def/NumberField_AdelicLevel.html#L418) attached to the ideal $(N)$ of $\mathcal{O}_{\mathbb{Q}}$, and satisfies $\Psi(x)=(F\mid_2 \mathrm{ratArchGL2}\,x)(i)$ for every adelic $x$ whose finite part `glFin` is trivial and whose real component [`LanglandsTunnell.ratArchGL2`](def/LanglandsTunnell_DeltaLift.html#L16) has positive determinant. Let $p$ be a prime with $p\nmid N$ and let $\rho_0,\dots,\rho_p\in\mathrm{GL}_2(\mathbb{Q}_p)$ have underlying matrices $\begin{pmatrix}1&i\\0&p\end{pmatrix}$ for $i<p$ and $\begin{pmatrix}p&0\\0&1\end{pmatrix}$ for $i=p$. Finally let $h$ be an adelic element with `glFin` $h=1$ and $\mathrm{ratArchGL2}\,h\in\mathrm{GL}_2^{+}(\mathbb{R})$. Then $$\sum_{i=0}^{p}\Psi\bigl(h\cdot \mathrm{padicToAdelic}_p(\rho_i)^{-1}\bigr)=\Bigl(\bigl(\varepsilon(p)^{-1}\cdot U_p F+F\mid_2 \mathrm{diag}(p,1)\bigr)\Big|_2 \mathrm{ratArchGL2}\,h\Bigr)(i),$$ where [`ModularForm.heckeU 2 p`](def/ModularForm_HeckeOperator.html#L93) is the sum $\sum_{j<p}F\mid_2\begin{pmatrix}1&j\\0&p\end{pmatrix}$ and [`ModularForm.heckeDiagMatrix p`](def/ModularForm_HeckeOperator.html#L21) is $\mathrm{diag}(p,1)$, both as real slash actions in weight $2$, and $\mathrm{padicToAdelic}_p$ is the embedding of $\mathrm{GL}_2(\mathbb{Q}_p)$ into the adelic group supported at the place $p$.
--
--   This is the classical–adelic dictionary for the Hecke operator at a prime not dividing the level: the sum over the $p+1$ cosets of the adelic Hecke operator, evaluated on the lift of a weight-two form with nebentypus, is rewritten as a combination of the classical operator $U_p$ and the slash by $\mathrm{diag}(p,1)$. It is used in the computation of the $T_p$-eigenvalue of the adelic lift from the $q$-expansion coefficients of $F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCosets_sum_apply_eq_slash.lean

import Definitions.Def_CuspForm_AdelicLiftGamma1
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped ModularForm

theorem HeckeCosets.sum_apply_eq_slash
    {N : ℕ} [NeZero N] {ε : DirichletCharacter ℂ N} {F : CuspForm (CongruenceSubgroup.Gamma1 N) 2}
    (hε : CuspForm.HasNebentypus ε F)
    {Ψ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ}
    (hΨ : CuspForm.IsAdelicLiftOfGamma1 F Ψ)
    (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (ρ : Fin (p + 1) → GL (Fin 2) ℚ_[p])
    (hρ : ∀ i : Fin (p + 1), ((ρ i : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      if (i : ℕ) < p then !![(1 : ℚ_[p]), ((i : ℕ) : ℚ_[p]); 0, (p : ℚ_[p])]
      else !![(p : ℚ_[p]), 0; 0, 1])
    {h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ}
    (hh : NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1)
    (hpos : LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ) :
    ∑ i : Fin (p + 1), Ψ (h * AdelicDock.padicToAdelic p (ρ i)⁻¹) =
      (((ε (p : ZMod N))⁻¹ • ModularForm.heckeU 2 p ⇑F +
            (⇑F) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix p) ∣[(2 : ℤ)]
          LanglandsTunnell.ratArchGL2 h) UpperHalfPlane.I := by sorry
