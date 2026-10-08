-- Prove2me | Theorems.Thm_HScattered_Delsarte_proposition_3_1
-- name    : HScattered.Delsarte.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:34.021975+00:00
-- url     : https://prove2.me/theorems/dbc8edd5-0080-47c9-8f47-c3378b72e0e7
-- title:
--   Proposition 3.1 — under (⋄) the Delsarte dual W + Γ^⊥ is k-dimensional
-- statement:
--   Work in the setting of §3, with $k=\dim_{\mathbb F_{q^n}}\mathbb V=\dim_{\mathbb F_q}W$, $r=\dim_{\mathbb F_{q^n}}\Lambda$, and $U=\langle W,\Gamma\rangle_{\mathbb F_q}\cap\Lambda$. Suppose that $U$ is a $k$-dimensional $\mathbb F_q$-subspace of $\Lambda$ with $k>r$ and that
--
--   $$
--   \dim_{\mathbb F_q}(M\cap U)<k-1 \quad\text{for each hyperplane } M \text{ of } \Lambda. \tag{\diamond}
--   $$
--
--   Then $W+\Gamma^\perp$ is a $k$-dimensional $\mathbb F_q$-subspace of the quotient space $\mathbb V/\Gamma^\perp$, i.e. $\dim_{\mathbb F_q}\bar U=k$ for the Delsarte dual $\bar U$.
--
--   The proposition is what makes Definition 3.2 meaningful: under ($\diamond$) the passage $W\mapsto W+\Gamma^\perp$ loses no dimension.
--
--   **Formalization Note** A hyperplane $M$ of $\Lambda$ is a `K`-subspace of `↥Λ` with $\dim M+1=\dim\Lambda$, and ($\diamond$) is written $\dim_{\mathbb F_q}(M\cap U)+1<k$ to avoid natural-number subtraction. The conclusion is `Module.finrank F D.dual = Module.finrank K 𝕍`.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 9, Proposition 3.1

import Mathlib
import Definitions.Def_HScattered_Delsarte_DelsarteSetting

namespace HScattered.Delsarte

/-- Proposition 3.1 (arXiv:1906.10590v2, p. 9): in the setting of §3, with
`k = dim_{𝔽_{qⁿ}} 𝕍 = dim_{𝔽_q} W` and `U = ⟨W, Γ⟩_{𝔽_q} ∩ Λ`, if `U` is `k`-dimensional, `k > r`,
and every hyperplane `M` of `Λ` satisfies `dim_{𝔽_q}(M ∩ U) < k − 1` (condition (⋄)), then
`Ū = W + Γ^⊥` is a `k`-dimensional `𝔽_q`-subspace of `𝕍 / Γ^⊥`. -/
theorem proposition_3_1 {F K 𝕍 : Type*} [Field F] [Field K] [Algebra F K]
    [AddCommGroup 𝕍] [Module K 𝕍] [Module F 𝕍] [IsScalarTower F K 𝕍]
    [Fintype F] [Fintype K] [FiniteDimensional K 𝕍]
    (D : DelsarteSetting F K 𝕍)
    (hUk : Module.finrank F D.U = Module.finrank K 𝕍)
    (hkr : Module.finrank K D.Λ < Module.finrank K 𝕍)
    (hdiamond : ∀ M : Submodule K D.Λ, Module.finrank K M + 1 = Module.finrank K D.Λ →
      Module.finrank F ↥(M.restrictScalars F ⊓ D.U) + 1 < Module.finrank K 𝕍) :
    Module.finrank F D.dual = Module.finrank K 𝕍 := by sorry

end HScattered.Delsarte
