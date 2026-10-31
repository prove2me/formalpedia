-- Prove2me | Theorems.Thm_MayersBC_effectProb_sub_le_two_norm_sub
-- name    : MayersBC.effectProb_sub_le_two_norm_sub
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:08.420364+00:00
-- url     : https://prove2.me/theorems/d82fb49b-1d97-49c1-8e58-196196eb20dd
-- title:
--   Section d, p.9 — the perturbation bound $|\Pr_{\varphi_0} - \Pr_{\varphi_1}| \le 2\sqrt{2(1-\langle\varphi_0|\varphi_1\rangle)} \le 4\sqrt\varepsilon$
-- statement:
--   Let $\varphi_0, \varphi_1$ be unit vectors, $G$ an effect ($0 \le G \le I$), and $\varepsilon$ a real number with $\operatorname{Re}\langle\varphi_0|\varphi_1\rangle \ge 1 - 2\varepsilon$. Then
--
--   $$
--   \big|\langle\varphi_0|G|\varphi_0\rangle - \langle\varphi_1|G|\varphi_1\rangle\big| \le 2\sqrt{\langle\varphi_0 - \varphi_1|G|\varphi_0 - \varphi_1\rangle},
--   \qquad
--   \sqrt{\langle\varphi_0 - \varphi_1|G|\varphi_0 - \varphi_1\rangle} \le \|\varphi_0 - \varphi_1\|,
--   $$
--
--   $$
--   \|\varphi_0 - \varphi_1\| = \sqrt{2\big(1 - \operatorname{Re}\langle\varphi_0|\varphi_1\rangle\big)},
--   $$
--
--   and
--
--   $$
--   2\sqrt{2\big(1 - \operatorname{Re}\langle\varphi_0|\varphi_1\rangle\big)} \le 4\sqrt{\varepsilon} .
--   $$
--
--   These are the steps of the page's display: $\sqrt{\langle v|G|v\rangle} = \|M_{1,ok} v\|$ for $v = \varphi_0 - \varphi_1$. In the paper $G = M_{1,ok}^\dagger M_{1,ok}$, where $M_{1,ok}$ collects the outcomes of Alice's and Bob's joint measurement that make Bob accept the bit $1$. The bound shows that preparing $\varphi_0$ instead of $\varphi_1$ changes the acceptance probability by at most $4\sqrt\varepsilon$.
--
--   Differences from the source:
--   - encoding: the collapse operator M_{1,ok} and ‖M_{1,ok}|φ⟩‖², ‖M_{1,ok}(|φ0⟩ − |φ1⟩)‖ → an effect G and effectProb G |φ⟩⟨φ| = ⟨φ|G|φ⟩, √(effectProb G |φ0 − φ1⟩⟨φ0 − φ1|); reason: ‖M φ‖² = ⟨φ|M†M|φ⟩ with M†M an effect, and every effect G is (√G)†√G
--   - generalization: a real overlap ⟨φ0|φ1⟩ (the purifications of p.8) → Re⟨φ0|φ1⟩ for arbitrary unit vectors; reason: for a real overlap Re⟨φ0|φ1⟩ = ⟨φ0|φ1⟩, so the statement specializes to the page's
--   - encoding: ⟨φ0|φ1⟩ ≥ 1 − 2ε, from p.8, used for the last step ≤ 4√ε → the hypothesis 1 − 2ε ≤ Re⟨φ0|φ1⟩; reason: the page's last inequality uses exactly this fact; for ε ≥ 1 it holds for all unit vectors, so the other three clauses are unrestricted
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section d, p.9 (display)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
open QAlgorithms

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section d, p.9 (display):
`|Pr(T_1(Y) = ok | Φ = φ_0) − Pr(T_1(Y) = ok | Φ = φ_1)| = | ‖M_{1,ok}|φ_0⟩‖² − ‖M_{1,ok}|φ_1⟩‖² |
≤ 2 × ‖M_{1,ok}(|φ_0⟩ − |φ_1⟩)‖ ≤ 2 × ‖|φ_0⟩ − |φ_1⟩‖ = 2 × √(2(1 − ⟨φ_0|φ_1⟩)) ≤ 4√ε`.
For unit vectors `φ_0, φ_1` with `Re⟨φ_0|φ_1⟩ ≥ 1 − 2ε` (p.8) and an effect `0 ≤ G ≤ I`, every
step of the display: `|⟨φ_0|G|φ_0⟩ − ⟨φ_1|G|φ_1⟩| ≤ 2√⟨φ_0 − φ_1|G|φ_0 − φ_1⟩` (the page's
`2‖M_{1,ok}(|φ_0⟩ − |φ_1⟩)‖`), `√⟨φ_0 − φ_1|G|φ_0 − φ_1⟩ ≤ ‖φ_0 − φ_1‖`,
`‖φ_0 − φ_1‖ = √(2(1 − Re⟨φ_0|φ_1⟩))`, and `2√(2(1 − Re⟨φ_0|φ_1⟩)) ≤ 4√ε`.

**Formalization Note.** The collapse operator `M_{1,ok}` enters through `G = M_{1,ok}† M_{1,ok}`,
an effect, so `‖M_{1,ok} v‖² = ⟨v|G|v⟩ = effectProb G |v⟩⟨v|` for every vector `v`. The paper's
overlap is real (the purifications of p.8 are chosen so); for general vectors the real part
appears. The overlap
bound `Re⟨φ_0|φ_1⟩ ≥ 1 − 2ε` is the hypothesis the page's last step uses; it holds for all unit
vectors when `ε ≥ 1`, so the first three clauses are unrestricted. -/
theorem effectProb_sub_le_two_norm_sub {κ : Type} [Fintype κ] [DecidableEq κ]
    (φ0 φ1 : EuclideanSpace ℂ κ) (h0 : IsState φ0) (h1 : IsState φ1) (G : Matrix κ κ ℂ)
    (hG : IsEffect G) (ε : ℝ) (hov : 1 - 2 * ε ≤ (inner ℂ φ0 φ1).re) :
    |effectProb G (pureDensity φ0) - effectProb G (pureDensity φ1)| ≤
        2 * Real.sqrt (effectProb G (pureDensity (φ0 - φ1))) ∧
      Real.sqrt (effectProb G (pureDensity (φ0 - φ1))) ≤ ‖φ0 - φ1‖ ∧
      ‖φ0 - φ1‖ = Real.sqrt (2 * (1 - (inner ℂ φ0 φ1).re)) ∧
      2 * Real.sqrt (2 * (1 - (inner ℂ φ0 φ1).re)) ≤ 4 * Real.sqrt ε := by sorry

end MayersBC
