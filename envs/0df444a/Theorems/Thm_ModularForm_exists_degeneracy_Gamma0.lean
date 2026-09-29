-- Prove2me | Theorems.Thm_ModularForm_exists_degeneracy_Gamma0
-- name    : ModularForm.exists_degeneracy_Gamma0
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/977cb42e-8443-5be3-bfc1-1aa296405e93
-- title:
--   Degeneracy map f(τ)↦ f(dτ) from Γ₀(M) to Γ₀(N)
-- statement:
--   Let $k$ be an integer and $M, N, d$ natural numbers with $N$ nonzero, and suppose $d\,M \mid N$ (so in particular $d \neq 0$ and $M \neq 0$). Write `heckeDiagMatrix d` for the element of $\mathrm{GL}_2(\mathbb{R})$ which is the identity when $d = 0$ and otherwise the upper triangular matrix $\begin{pmatrix} d & 0 \\ 0 & 1\end{pmatrix}$ (viewed as invertible since $d \cdot 1 \neq 0$), acting on the upper half plane by $\tau \mapsto d\tau$. Then for every modular form $f$ of weight $k$ for the congruence subgroup $\Gamma_0(M)$, regarded as a subgroup of $\mathrm{GL}_2(\mathbb{R})$, there exists a modular form $g$ of weight $k$ for $\Gamma_0(N)$ whose underlying function is exactly $\tau \mapsto f(\,$`heckeDiagMatrix d`$\cdot \tau)$, that is, $g(\tau) = f(d\tau)$ with no normalising constant. The assertion is the existence of such a $g$, not a map or a linear embedding of spaces of forms.
--
--   This is the degeneracy (level-raising) map $V_d$ of Atkin–Lehner theory, in the form $f(\tau) \mapsto f(d\tau)$, sending weight-$k$ forms on $\Gamma_0(M)$ to weight-$k$ forms on $\Gamma_0(N)$ whenever $dM \mid N$; such maps produce the oldforms of level $N$ coming from level $M$. It is used throughout the project wherever a form of small level must be regarded, after rescaling of the variable, as a form of larger level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_degeneracy_Gamma0.lean

import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.exists_degeneracy_Gamma0 {k : ℤ} {M N d : ℕ} [NeZero N] (hd : d * M ∣ N) (f : ModularForm (CongruenceSubgroup.Gamma0 M) k) : ∃ g : ModularForm (CongruenceSubgroup.Gamma0 N) k, ⇑g = fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ) := by sorry
