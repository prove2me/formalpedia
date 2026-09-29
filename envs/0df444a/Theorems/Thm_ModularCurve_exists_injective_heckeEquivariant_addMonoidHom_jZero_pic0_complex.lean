-- Prove2me | Theorems.Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex
-- name    : ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/3df3b532-8e31-541f-b804-f2eda212f055
-- title:
--   Base change of J₀(N) from ℚ̄ to ℂ
-- statement:
--   Let $N$ be a nonzero natural number. Write $F_N =$ `modularFunctionFieldFull N` for the subfield of $\mathbb{Q}(\!(q)\!)$ generated over $\mathbb{Q}$ by the divisor expansions at level $N$, and for a field $L$ over $\mathbb{Q}$ write $L F_N$ for `laurentBaseChange L F_N`, the subfield of $L(\!(q)\!)$ generated over $L$ by the coefficientwise image of $F_N$; $\mathrm{Pic}^0(L F_N/L)$ is the group of finitely supported $\mathbb{Z}$-valued functions on the places of $L F_N$ over $L$ of total degree zero, modulo those that are principal. Assume `HeckeInputsAll N`, i.e. for every prime $\ell$ the integrality, finiteness, fundamental-identity and norm-formula data `HeckeInputsAlong` for the two degeneracy maps from level $N$ to level $N\ell$ over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, and assume `HeckeInputsAlong ℂ N ℓ`, the same data over $\mathbb{C}$, for every prime $\ell$. Then there is an additive homomorphism $\iota \colon \mathrm{Pic}^0(\overline{\mathbb{Q}} F_N/\overline{\mathbb{Q}}) \to \mathrm{Pic}^0(\mathbb{C} F_N/\mathbb{C})$ such that $\iota$ is injective, every element of finite additive order of the target lies in the range of $\iota$, and for every prime $\ell$ and every $x$ in the source, $\iota$ carries `heckeOperatorBar N ℓ` applied to $x$ to `heckeOperatorAlong ℂ N ℓ` applied to $\iota(x)$, where these operators are the correspondence-induced endomorphisms attached to the respective Hecke inputs (and $0$ when the inputs fail).
--
--   Classically this is the conorm map on degree-zero divisor classes along the constant field extension $\overline{\mathbb{Q}} F_N \subseteq \mathbb{C} F_N$ induced by an embedding $\overline{\mathbb{Q}} \hookrightarrow \mathbb{C}$, i.e. pullback of divisor classes along $X_0(N)_{\mathbb{C}} \to X_0(N)_{\overline{\mathbb{Q}}}$: it is injective, Hecke-equivariant, and its image contains all torsion. It is used to transport the analytic description of $\mathrm{Pic}^0$ over $\mathbb{C}$ (as the dual of weight-two cusp forms modulo the period lattice) to the Jacobian over $\overline{\mathbb{Q}}$, in [`ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice`](thm.html#ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex
    (N : ℕ) [NeZero N]
    (hin : ModularCurve.HeckeInputsAll N)
    (hinC : ∀ ℓ : Nat.Primes,
      haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; ModularCurve.HeckeInputsAlong ℂ N ℓ) :
    ∃ ι : ModularCurve.JZero N →+
        AlgebraicCurve.Pic0 ℂ
          (ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)),
      Function.Injective ι ∧
      (∀ z, IsOfFinAddOrder z → z ∈ ι.range) ∧
      ∀ (ℓ : Nat.Primes) (x : ModularCurve.JZero N),
        ι (ModularCurve.heckeOperatorBar N ℓ x) =
          (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; ModularCurve.heckeOperatorAlong ℂ N ℓ)
            (ι x) := by sorry
