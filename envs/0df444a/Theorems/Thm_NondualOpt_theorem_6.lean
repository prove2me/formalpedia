-- Prove2me | Theorems.Thm_NondualOpt_theorem_6
-- name    : NondualOpt.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:03:35.329427+00:00
-- url     : https://prove2.me/theorems/2d242829-0919-49fd-a7b8-56da18043a8c
-- title:
--   Theorem 6 (first part) — sfat bounds on the max-regret value
-- statement:
--   Under Assumption 3, let $T\ge1$, $\Lambda=\Lambda_{X,H}$ and $\mathrm{sfat}^{X,H}_\eta=\mathrm{sfat}_\eta(L_{X,H})$. There are universal constants $C,c,\gamma>0$ such that
--   $$
--   \sup_{\alpha>0}\frac\alpha2\Big(\frac{\mathrm{sfat}^{X,H}_\alpha}T\wedge1\Big)\le\frac{V^{\max}_{X,H,T}}T\le\inf_{0<\alpha\le\Lambda}\Big\{C\alpha+\frac CT\Big[\Lambda\Big(1+\log\frac{e\Lambda}\alpha\Big)+\int_\alpha^\Lambda\mathrm{sfat}^{X,H}_{c\beta}\log^\gamma\Big(\frac{eT\Lambda}\beta\Big)d\beta\Big]\Big\}.
--   $$
--   The value of the max-regret game, and through Lemma 2 the first-order oracle complexity, is controlled from both sides by the sequential fat-shattering dimension of the linear pairing class $L_{X,H}$. In the $(p,q)$ case, Theorem 30 makes the upper bound explicit and gives the rate of Corollary 7.
--
--   Differences from the source:
--   - generalization: E a real Banach space, H ⊆ E∗ bounded with the duality pairing, X closed and bounded with 0 ∈ X (§2 standing setting) → real vector spaces E, F with an abstract bilinear pairing, Λ_{X,H} < ∞, no closedness or boundedness of X and no 0 ∈ X; reason: the proofs use H only through pairings ⟨g, u⟩ and the bound Λ_{X,H} (footnote 7); the duality pairing between E∗ and E with bounded H is the instance F = E∗
--   - reading: the distributions r_t, s_t of ① in Assumption 3, with the measurable η-minimizer clause → finitely supported laws; the selection clause is not stated; reason: footnote 6, p.9: finitely supported adversarial laws suffice for the minimax interchanges; for such laws expectations are finite sums and the selection clause is automatic
--   - encoding: sup over α > 0 and inf over 0 < α ≤ Λ of bounds on V^max/T → each inequality for every such α, both sides multiplied by T; V^max extended-real; reason: no junk value of an empty infimum when Λ = 0
--   - encoding: ∫_α^Λ sfat_{cβ} log^γ(eTΛ/β) dβ → lower Lebesgue integral in [0, ∞] over (α, Λ] with sfat in ℕ ∪ {∞}; reason: the integrand may be infinite
--   - encoding: universal constants C, c, γ → chosen before the spaces, the sets and T (spaces in one universe); reason: the paper's quantifier order
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Theorem 6, p.11 ("the first part of Theorem 6", p.12)

import Mathlib
import Definitions.Def_NondualOpt_crossDuality
import Definitions.Def_NondualOpt_Vmax
import Definitions.Def_NondualOpt_Assumption3
import Definitions.Def_NondualOpt_linClass
import Definitions.Def_NondualOpt_sfat

open scoped ENNReal

universe u

namespace NondualOpt

/-- **Theorem 6 (first part).** Under Assumption 3, let `T ≥ 1`, `Λ = Λ_{X,H}` and
`sfat^{X,H}_η = sfat_η(L_{X,H})`. There are universal constants `C, c, γ > 0` such that
`sup_{α > 0} (α/2)(sfat^{X,H}_α/T ∧ 1) ≤ V^max_{X,H,T}/T ≤
inf_{0 < α ≤ Λ} {Cα + (C/T)[Λ(1 + log(eΛ/α)) + ∫_α^Λ sfat^{X,H}_{cβ} log^γ(eTΛ/β) dβ]}`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Theorem 6, p.11 (the display; the paper
calls it "the first part of Theorem 6", p.12).

**Formalization Note.** (i) The constants are chosen before the spaces, sets and horizon.
(ii) The pairing is abstract (`F` in place of `E∗`; footnote 7); Assumption 3 replaces "H bounded"
by `Λ < ∞` and reads ① with finitely supported laws (see `Assumption3`). The standing §2
conditions on `X` (closed, bounded, `0 ∈ X`) are not assumed. (iii) The supremum over `α > 0` and
the infimum over `0 < α ≤ Λ` are stated for every such `α`, and both sides are multiplied by `T`;
`V^max` is `EReal`-valued. (iv) The upper bound's integral is a lower Lebesgue integral in `ℝ≥0∞`
over `(α, Λ]`, and `sfat` enters as an extended natural number. -/
theorem theorem_6 :
    ∃ C c γ : ℝ, 0 < C ∧ 0 < c ∧ 0 < γ ∧
      ∀ (E F : Type u) [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
        (pair : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (X : Set E) (H : Set F) (T : ℕ), 1 ≤ T →
        Assumption3 pair X H T →
        (∀ α : ℝ, 0 < α →
          (((T : ℝ) * (α / 2 *
              (min ((sfat (linClass pair X H) α : ℝ≥0∞) / (T : ℝ≥0∞)) 1).toReal) : ℝ) : EReal) ≤
            Vmax pair X H T) ∧
        (∀ α : ℝ, 0 < α → α ≤ crossDuality pair X H →
          Vmax pair X H T ≤
            (((T : ℝ≥0∞) * (ENNReal.ofReal (C * α + C / T * (crossDuality pair X H *
                (1 + Real.log (Real.exp 1 * crossDuality pair X H / α)))) +
              ENNReal.ofReal (C / T) * ∫⁻ β in Set.Ioc α (crossDuality pair X H),
                (sfat (linClass pair X H) (c * β) : ℝ≥0∞) *
                  ENNReal.ofReal (Real.log (Real.exp 1 * T * crossDuality pair X H / β) ^ γ)) :
              ℝ≥0∞) : EReal)) := by sorry

end NondualOpt
