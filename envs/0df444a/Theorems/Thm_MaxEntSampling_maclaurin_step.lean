-- Prove2me | Theorems.Thm_MaxEntSampling_maclaurin_step
-- name    : MaxEntSampling.maclaurin_step
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:58:19.664018+00:00
-- url     : https://prove2.me/theorems/4740582b-ce30-4ca4-8b7e-f29b3412bb9a
-- title:
--   Proof of Theorem 5, Maclaurin step — $E_s(\hat x)\le(s/n)^s\binom ns$ on $D$
-- statement:
--   For every $\hat x\in D$, that is $\hat x\in[0,1]^n$ with $\sum_{i\in[n]}\hat x_i=s$,
--
--   $$
--   E_s(\hat x) = \sum_{S\in\binom{[n]}{s}}\prod_{i\in S}\hat x_i \;\le\; \Bigl(\frac sn\Bigr)^s\binom ns .
--   $$
--
--   Dividing $\exp\Gamma_s(\cdot)$ by both sides gives the second inequality of the proof of Theorem 5, where the paper attributes it to Maclaurin's inequality (Lin and Trudinger 1994). It is the source of the factor $\bigl((s/n)^s\binom ns\bigr)^{-1}$ in the approximation bound.
--
--   Differences from the source:
--   - generalization: exp Γ_s(Σ x̂_i v_i v_iᵀ)/E_s(x̂) ≥ ((s/n)^s C(n,s))^{−1} exp Γ_s(Σ x̂_i v_i v_iᵀ), under the hypotheses of Theorem 5 → E_s(x̂) ≤ C(n,s) (s/n)^s for every x̂ ∈ D, with no hypothesis on V, d or s; reason: multiplying the bound by exp Γ_s ≥ 0 and dividing by E_s(x̂) > 0 gives the page's inequality; the bound holds for all n, s
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, proof of Theorem 5, p.15 (PDF p.15)

import Mathlib
import Definitions.Def_MaxEntSampling_feasD
import Definitions.Def_MaxEntSampling_esymm

namespace MaxEntSampling

/-- **Maclaurin step in the proof of Theorem 5: `E_s(x̂) ≤ (s/n)^s C(n,s)` on `D`.**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, proof of Theorem 5, p.15 (PDF p.15): the second inequality of the chain,
"exp[Γs(Σ_{i∈[n]} x̂i vi vi^⊤)] / Σ_{S̄∈C([n],s)} ∏_{i∈S̄} x̂i ≥ ((s/n)^s C(n,s))^{−1}
exp[Γs(Σ_{i∈[n]} x̂i vi vi^⊤)] … the second one is from Maclaurin's inequality (Lin and
Trudinger 1994)".

For every `x̂` in the feasible set `D` of PC (9) (`x̂ ∈ [0,1]ⁿ`, `Σ_i x̂_i = s`), the elementary
symmetric polynomial satisfies `E_s(x̂) = Σ_{|S|=s} ∏_{i∈S} x̂_i ≤ C(n,s) (s/n)^s`.

**Formalization Note.** The page's inequality between the two displayed quantities follows from
this bound on its denominator by multiplying with `exp Γ_s ≥ 0`; this is the content of the step
that Maclaurin's inequality supplies. The bound holds for every `n, s` (for `s > n` the set `D`
is empty), so no further standing hypothesis is assumed. -/
theorem maclaurin_step {n : ℕ} (s : ℕ) (x : Fin n → ℝ) (hx : x ∈ feasD n s) :
    esymm s x ≤ (n.choose s : ℝ) * ((s : ℝ) / n) ^ s := by sorry

end MaxEntSampling
