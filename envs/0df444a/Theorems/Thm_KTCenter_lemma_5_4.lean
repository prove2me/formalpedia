-- Prove2me | Theorems.Thm_KTCenter_lemma_5_4
-- name    : KTCenter.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:28.245875+00:00
-- url     : https://prove2.me/theorems/74c58ae5-e748-4d49-a564-567cb8d209c5
-- title:
--   Lemma 5.4 — finite keys preserve a nearby ranking within $2\beta W$
-- statement:
--   Let $(w_v)$ be nonnegative integers and $0<\beta<1$.
--
--   1. For every ranking $\tau$ with $\mathrm{pos}_\tau(v)\in I_v$ for all $v$, there is an allowed assignment $p$ with $\mathcal K(\sigma_p,\tau)\le2\beta W$.
--   2. If some ranking $\tau$ has $\mathrm{Obj}(\Pi,\tau)\le(1+2\delta)R^*$ and $|\mathrm{pos}_\tau(v)-v|\le w_v$ for all $v$ (the guarantee of Lemma 4.1), then there is an allowed assignment $p$ with
--   $$\mathcal K(\sigma_p,\pi_i)\le(1+2\delta)R^*+2\beta W\qquad(i\in[n]).$$
--
--   Differences from the source:
--
--   - generalization: allowances w_v = 5 deg_{E_J}(v) of the fixed tuple → arbitrary nonnegative integers w_v; reason: Algorithms 2 and 3 take arbitrary nonnegative integer allowances and the proofs use nothing else; it specializes to the source
--   - reading: "the fixed tuple satisfies the guarantee of Lemma 4.1" → there is a ranking τ with radius ≤ (1+2δ)R* and |pos_τ(v) − v| ≤ w_v; reason: this is the guarantee (9) for the tuple whose allowances are w
--   - encoding: assignment on U extended by p_v = v outside U → full key vector in ∏ P_v; reason: P_v = {v} when w_v = 0, so the two sets coincide
--   - generalization: δ > 0 fixed in (15) → any real δ in the second clause; reason: the proof is the triangle inequality K(σ_p, π_i) ≤ K(σ_p, τ) + K(τ, π_i) and never uses the sign of δ; it specializes to the source at δ > 0
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Lemma 5.4, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_KTCenter_Instance
import Definitions.Def_KTCenter_KeyDomains

namespace KTCenter

/-- **Lemma 5.4** (Finite keys preserve a nearby ranking), p.26 (PDF p.28).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** `τ` is any ranking with `pos_τ(v) ∈ I_v` (p.26). The second clause reads "the
fixed tuple satisfies the guarantee of Lemma 4.1": a ranking with `|pos_τ(v) − v| ≤ w_v`, as (9), and
radius at most `(1 + 2δ)R*`. An assignment `p` is a full key vector (see `assignments`). -/
theorem lemma_5_4 (I : Instance) (w : Fin I.d → ℕ) (β : ℚ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ τ : Equiv.Perm (Fin I.d), (∀ v, ((lab (τ⁻¹ v) : ℤ) : ℚ) ∈ keyInterval w v) →
      ∃ p ∈ assignments w β,
        (dist (sortRanking p) τ : ℚ) ≤ 2 * β * (totalW w : ℚ)) ∧
    ∀ δ : ℝ,
      (∃ τ : Equiv.Perm (Fin I.d), (obj I τ : ℝ) ≤ (1 + 2 * δ) * (optRadius I : ℝ) ∧
        ∀ v, |lab (τ⁻¹ v) - lab v| ≤ (w v : ℤ)) →
      ∃ p ∈ assignments w β, ∀ i : Fin I.n,
        (dist (sortRanking p) (I.π i) : ℝ) ≤
          (1 + 2 * δ) * (optRadius I : ℝ) + 2 * (β : ℝ) * (totalW w : ℝ) := by sorry

end KTCenter
