-- Prove2me | Theorems.Thm_ModularForm_rescaleSlash_slash_eq_self_of_mem_Gamma0
-- name    : ModularForm.rescaleSlash_slash_eq_self_of_mem_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/bc10ebd6-1010-56aa-a001-66c19e51e282
-- title:
--   Slash by diag(d,1) carries Γ₀(R)-invariance to Γ₀(M)
-- statement:
--   Let $R$, $M$, $d$ be natural numbers with $M$ nonzero and $d\cdot R \mid M$, let $k$ be an integer weight, and let $f:\mathbb{H}\to\mathbb{C}$ be a function on the upper half-plane. Assume $f$ is invariant in weight $k$ under the image of $\Gamma_0(R)$ in $\mathrm{GL}_2(\mathbb{R})$, that is, the weight-$k$ slash action satisfies $f\mid_k\gamma' = f$ for every element $\gamma'$ of $\mathrm{GL}_2(\mathbb{R})$ lying in $\Gamma_0(R)$. Write $\alpha_d$ for the element [`ModularForm.heckeDiagMatrix d`](def/ModularForm_HeckeOperator.html#L21) of $\mathrm{GL}_2(\mathbb{R})$, which by definition is the identity matrix when $d=0$ and otherwise the upper triangular matrix $\begin{pmatrix} d & 0\\ 0 & 1\end{pmatrix}$. Then for every $\gamma\in\mathrm{GL}_2(\mathbb{R})$ lying in the image of $\Gamma_0(M)$ one has $$\bigl(f\mid_k \alpha_d\bigr)\mid_k\gamma \;=\; f\mid_k\alpha_d .$$ Thus the slash translate of $f$ by $\mathrm{diag}(d,1)$ is invariant in weight $k$ under $\Gamma_0(M)$. No holomorphy, growth or automorphy condition beyond the stated $\Gamma_0(R)$-invariance is imposed on $f$.
--
--   This is the level-raising invariance clause underlying the rescaling degeneracy map $V_d$, which sends a form of level $R$ to the form $\tau\mapsto f(d\tau)$ of level $M$ whenever $dR \mid M$ (up to the normalising factor $d^{k-1}$ built into the slash action). It is used in the construction of the mod-$p$ level-raising operator, being cited by [`ModPForms.heckeV_mem_modPMod_mul`](thm.html#ModPForms.heckeV_mem_modPMod_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_rescaleSlash_slash_eq_self_of_mem_Gamma0.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped ModularForm

theorem ModularForm.rescaleSlash_slash_eq_self_of_mem_Gamma0 {R M d : ℕ} [NeZero M]
    (hdRM : d * R ∣ M) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 R : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      SlashAction.map k γ f = f)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hγ : γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    SlashAction.map k γ (SlashAction.map k (ModularForm.heckeDiagMatrix d) f)
      = SlashAction.map k (ModularForm.heckeDiagMatrix d) f := by sorry
