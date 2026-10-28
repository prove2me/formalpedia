-- Prove2me | Theorems.Thm_NonAbelianDMNRG_Recursion_cg_sum_rule
-- name    : NonAbelianDMNRG.Recursion.cg_sum_rule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:15.682418+00:00
-- url     : https://prove2.me/theorems/aebd7b15-6471-4447-b778-f8efa294d387
-- title:
--   p. 7, trace over the local states — $\sum_{q^z,Q'^z}\langle q q^z;QQ^z|Q'Q'^z\rangle\langle q q^z;QQ^{z\prime}|Q'Q'^z\rangle^* = \frac{\dim Q'}{\dim Q}\delta_{Q^zQ^{z\prime}}$
-- statement:
--   Let $G$ be a group and $\pi_q, \pi_Q, \pi_{Q'}$ unitary representations of $G$ of dimensions $\dim q$, $\dim Q$, $\dim Q'$, with $\pi_Q$ irreducible. Let $C$ be a $(\dim q\cdot\dim Q)\times\dim Q'$ matrix with entries $\langle q\,q^z; Q\,Q^z\mid Q'\,Q'^z\rangle$ (rows indexed by the pair $(q^z, Q^z)$, local index first) such that
--   1. $C^\dagger C = 1$, and
--   2. $(\pi_q(g)\otimes\pi_Q(g))\,C = C\,\pi_{Q'}(g)$ for all $g\in G$.
--
--   Then tracing $CC^\dagger$ over the local factor gives a multiple of the identity:
--   $$
--   \sum_{q^z}\sum_{Q'^z} \langle q\,q^z; Q\,Q^z\mid Q'\,Q'^z\rangle\, \overline{\langle q\,q^z; Q\,Q^{z\prime}\mid Q'\,Q'^z\rangle} = \frac{\dim Q'}{\dim Q}\,\delta_{Q^z, Q^{z\prime}} .
--   $$
--
--   This identity produces the factor $\dim(\tilde\imath)/\dim(u)$ in the recursion (45) when the local states of site $n$ are traced out of a canonical-basis dyad.
--
--   **Formalization Note** The left-hand side is written as the published partial trace over the left factor, `WildeQIT.partialTraceLeft`, of $CC^\dagger$. Irreducibility of $\pi_Q$ (which forces $\dim Q>0$) is the only irreducibility needed.
-- source:
--   Tóth, Moca, Legeza, Zaránd, Density matrix numerical renormalization group for non-Abelian symmetries, arXiv:0802.4332v1, p. 7, the step from (44) to (45) ("we can trace over the local states at site n using the recursion relation Eq. (21)")

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_NonAbelianDMNRG_Recursion_Multiplets
open Matrix
open scoped Kronecker

namespace NonAbelianDMNRG.Recursion

/-- **p. 7, the trace over the local states (dimension factor).** If `π Q` is irreducible and the
Clebsch–Gordan matrix `C = cg q Q Q'` is an isometry intertwining `π q ⊗ π Q` with `π Q'`, then
tracing `C C⁺` over the local (left) factor gives `dim Q' / dim Q` times the identity:
`Σ_{q^z, Q'^z} ⟨q q^z; Q Q^z | Q' Q'^z⟩ ⟨q q^z; Q Q^z' | Q' Q'^z⟩* = (dim Q' / dim Q) δ_{Q^z, Q^z'}`. -/
theorem cg_sum_rule {G : Type} [Group G] {Lab : Type} (dim : Lab → ℕ)
    (π : (Q : Lab) → G →* Matrix.unitaryGroup (Fin (dim Q)) ℂ)
    (q Q Q' : Lab) (hirr : Representation.IsIrreducible (labelRep dim π Q))
    (C : Matrix (Fin (dim q) × Fin (dim Q)) (Fin (dim Q')) ℂ)
    (hiso : Cᴴ * C = 1)
    (hint : ∀ g : G,
      ((π q g : Matrix (Fin (dim q)) (Fin (dim q)) ℂ) ⊗ₖ
          (π Q g : Matrix (Fin (dim Q)) (Fin (dim Q)) ℂ)) * C =
        C * (π Q' g : Matrix (Fin (dim Q')) (Fin (dim Q')) ℂ)) :
    WildeQIT.partialTraceLeft (C * Cᴴ) = ((dim Q' : ℂ) / (dim Q : ℂ)) • 1 := by sorry

end NonAbelianDMNRG.Recursion
