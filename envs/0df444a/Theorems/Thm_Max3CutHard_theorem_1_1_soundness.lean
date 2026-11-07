-- Prove2me | Theorems.Thm_Max3CutHard_theorem_1_1_soundness
-- name    : Max3CutHard.theorem_1_1_soundness
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:49:37.927651+00:00
-- url     : https://prove2.me/theorems/f6245e44-fad1-4c2a-a0ed-e871211e5386
-- title:
--   Proof of Theorem 1.1 — soundness: $\mathrm{cut}\le\tfrac{50}3+2(\mathrm{val}(\sigma)+\mathrm{val}(-\sigma))$
-- statement:
--   Let $\Phi$ be a balanced role-separated instance (weights $\lambda_e\ge0$ summing to $1$), $J=J(\Phi)$ the reduction graph for the family $(2E,N,N)$, $\chi$ any 3-colouring of $J$ and $\sigma$ the assignment it induces on the variables of $\Phi$ (colours read in $\mathbb Z_3$). Then
--
--   $$\mathrm{cut}_\chi(J)\ \le\ \frac{50}{3}+2\big(\mathrm{val}_\Phi(\sigma)+\mathrm{val}_\Phi(-\sigma)\big),$$
--
--   and if $\mathrm{val}(\Phi)\le\frac13+\varepsilon$, then
--
--   $$\mathrm{cut}_\chi(J)\ \le\ \Big(\frac9{10}+\frac\varepsilon5\Big)w(J).$$
--
--   This is the soundness half of the proof of Theorem 1.1; $-\sigma$ is the pointwise negation in $\mathbb Z_3$.
--
--   Differences from the source:
--   - generalization: ε > 0 (the ε of Theorem 2.1) → every real ε; reason: the source's ε > 0 is the special case; ε = 0 is included, and for ε < 0 the hypothesis on val(Φ) cannot hold (1/3 ≤ val(Φ) ≤ 1 for every weighted role-separated instance)
--   - encoding: colours [k] and ℤ₃, primaries p1, p2, p3, tuples (x1, x2, x3) → Fin k and ZMod 3 (= Fin 3), indices 0, 1, 2; reason: Lean convention; same instances
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Proof of Theorem 1.1, soundness, p.6

import Mathlib
import Definitions.Def_Max3CutHard_J
import Definitions.Def_Max3CutHard_family0
import Definitions.Def_Max3CutHard_wR
import Definitions.Def_Max3CutHard_cutR
import Definitions.Def_Max3CutHard_WInst_IsWeighting
import Definitions.Def_Max3CutHard_WInst_Balanced
import Definitions.Def_Max3CutHard_WInst_val

namespace Max3CutHard

/-- **Proof of Theorem 1.1, soundness.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Proof of Theorem 1.1, p.6: "Soundness: let `χ` be
any colouring and `σ` the assignment it induces on the variables of `Φ`. By (2) and (3),
`cut_χ(J) ≤ Σ_e λ_e β_{t_e} + 2 Σ_e λ_e([s_e = t_e] + [s_e = −t_e]) = 50/3 + 2(val_Φ(σ) + val_Φ(−σ))`,
where `s_e = σ(u_e) + σ(w_e) + σ(w′_e)`, because `−σ` satisfies `e` iff `−s_e = t_e`. If
`val(Φ) ≤ 1/3 + ε`, both values are at most `1/3 + ε`, so
`cut_χ(J) ≤ 50/3 + 4/3 + 4ε = 18 + 4ε = (9/10 + ε/5) w(J)`."

**Formalization Note.** `J` is built from `(2E, N, N)`; colours `Fin 3 = ℤ₃`, so `σ` is `χ` on the
variable vertices and `−σ` its pointwise negation in `ℤ₃`. Every balanced weighted instance,
every colouring, every real `ε`. -/
theorem theorem_1_1_soundness {U W : Type} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (Φ : WInst U W) (hΦ : Φ.IsWeighting) (hbal : Φ.Balanced) (χ : JVert Φ family0 → Fin 3) :
    cutR χ (J Φ family0) ≤ 50 / 3 + 2 *
      (Φ.valAt (fun u => χ (Sum.inl u)) (fun w => χ (Sum.inr (Sum.inl w))) +
        Φ.valAt (fun u => -χ (Sum.inl u)) (fun w => -χ (Sum.inr (Sum.inl w)))) ∧
    ∀ ε : ℝ, Φ.val ≤ 1 / 3 + ε → cutR χ (J Φ family0) ≤ (9 / 10 + ε / 5) * wR (J Φ family0) := by sorry

end Max3CutHard
