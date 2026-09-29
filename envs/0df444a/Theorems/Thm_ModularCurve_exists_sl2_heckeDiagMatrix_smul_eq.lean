-- Prove2me | Theorems.Thm_ModularCurve_exists_sl2_heckeDiagMatrix_smul_eq
-- name    : ModularCurve.exists_sl2_heckeDiagMatrix_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/6bea930f-bce9-5be9-a811-f44a172afd10
-- title:
--   Conjugating Γ₀(N) past diag(N,1) with equal denominators
-- statement:
--   Let $N$ be a natural number with $N \neq 0$, and let $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lie in the congruence subgroup $\Gamma_0(N)$, i.e. the reduction of its lower-left entry modulo $N$ vanishes. Write $\delta_N$ for [`ModularForm.heckeDiagMatrix N`](def/ModularForm_HeckeOperator.html#L21), which for $N \neq 0$ is the element of $\mathrm{GL}_2(\mathbb{R})$ given by the upper triangular matrix $\begin{pmatrix} N & 0 \\ 0 & 1\end{pmatrix}$ (and is $1$ when $N = 0$). The assertion is that there exists $\gamma' \in \mathrm{SL}_2(\mathbb{Z})$ with two properties. First, for every $\tau$ in the upper half plane, $\delta_N \cdot (\gamma \cdot \tau) = \gamma' \cdot (\delta_N \cdot \tau)$, the actions being the Möbius actions of $\mathrm{GL}_2(\mathbb{R})^+$ and of $\mathrm{SL}_2(\mathbb{Z})$ on the upper half plane; since $\delta_N$ acts by $\tau \mapsto N\tau$, this says $N(\gamma\tau) = \gamma'(N\tau)$. Second, the two automorphy denominators agree: for every $\tau$, $\mathrm{denom}(\gamma', N\tau) = \mathrm{denom}(\gamma, \tau)$, where $\mathrm{denom}(g, z) = g_{10} z + g_{11}$ and both matrices are viewed in $\mathrm{GL}_2(\mathbb{R})$ acting on $\mathbb{C}$-points. Thus the conjugate $\gamma'$ can be chosen so that no extra factor appears in the weight-$k$ automorphy factor.
--
--   This is the elementary bookkeeping behind the statement that $\tau \mapsto \Phi(N\tau)$ is a form on $\Gamma_0(N)$ of the same weight whenever $\Phi$ is a form of level one, the matching of denominators giving the matching of automorphy factors. It is used in the project's treatment of the $N$-scaled $q$-expansion, for instance for the ratio of discriminants $\Delta(N\tau)/\Delta(\tau)$, for the Fricke involution on such functions and for the construction of functions with prescribed cuspidal divisor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_sl2_heckeDiagMatrix_smul_eq.lean

import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_sl2_heckeDiagMatrix_smul_eq (N : ℕ) [NeZero N] (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : ∃ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ, (∀ τ : UpperHalfPlane, ModularForm.heckeDiagMatrix N • γ • τ = γ' • ModularForm.heckeDiagMatrix N • τ) ∧ ∀ τ : UpperHalfPlane, UpperHalfPlane.denom (γ' : Matrix.GeneralLinearGroup (Fin 2) ℝ) (((ModularForm.heckeDiagMatrix N • τ : UpperHalfPlane)) : ℂ) = UpperHalfPlane.denom (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (τ : ℂ) := by sorry
