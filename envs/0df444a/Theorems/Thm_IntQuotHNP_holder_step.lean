-- Prove2me | Theorems.Thm_IntQuotHNP_holder_step
-- name    : IntQuotHNP.holder_step
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:52:26.269181+00:00
-- url     : https://prove2.me/theorems/1819d756-be83-42e1-850d-f9e968a5320c
-- title:
--   Proof of Theorem 4.2 — Hölder step $u^N\Psi_X(u)\le\Psi_X(1)^{1-t}(X^N\Psi_X(X))^t\le B$
-- statement:
--   Let $\psi(s)=\sum_{\ell=1}^Lc_\ell s^{-r_\ell}$ with $c_\ell>0$, $r_\ell\ge0$. For $X>1$, $1<u<X$ and $t=\log u/\log X$,
--
--   1. $u^N\psi(u)=\sum_\ell c_\ell^{\,1-t}\bigl(c_\ell X^{N-r_\ell}\bigr)^t$;
--   2. $u^N\psi(u)\le\psi(1)^{1-t}\bigl(X^N\psi(X)\bigr)^t$;
--   3. if $\psi(1)\le B$ and $X^N\psi(X)\le B$, then $u^N\psi(u)\le B$.
--
--   This extends the endpoint bounds of Lemma 4.5 to the whole range $1\le u\le X$.
--
--   Differences from the source:
--   - generalization: ψ = Ψ_X of Lemma 4.5, X an integer, B its endpoint bound → any finite family c, r; real X, u; any B dominating both endpoints; reason: the display uses only the form of ψ, and Ψ_X with its B is an instance
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), proof of Theorem 4.2, p.24 (PDF p.25)

import Mathlib

namespace IntQuotHNP

/-- **Proof of Theorem 4.2: the Hölder step `u^N Ψ_X(u) ≤ Ψ_X(1)^{1−t}(X^N Ψ_X(X))^t ≤ B`.**
Kang, Lee, *Provable Recovery from Integer Quotients*, STOC 2027 submission (manuscript sha256
605f9dd3…), proof of Theorem 4.2, p.24 (PDF p.25): "write Ψ_X(u) = ∑_{ℓ=1}^L c_ℓ u^{−r_ℓ} for a
finite L, with c_ℓ > 0 and r_ℓ ≥ 0. For X > 1 and 1 < u < X, put t = log u/ log X. Hölder's
inequality gives u^NΨ_X(u) = ∑_{ℓ=1}^L c_ℓ^{1−t}(c_ℓX^{N−r_ℓ})^t ≤ (∑_{ℓ=1}^L c_ℓ)^{1−t}
(∑_{ℓ=1}^L c_ℓX^{N−r_ℓ})^t = Ψ_X(1)^{1−t}(X^NΨ_X(X))^t ≤ B."

For `ψ(s) = ∑_ℓ c_ℓ s^{−r_ℓ}` with `c_ℓ > 0`, `r_ℓ ≥ 0`, and `1 < u < X`, `t = log u / log X`:
1. `u^N ψ(u) = ∑_ℓ c_ℓ^{1−t}(c_ℓ X^{N−r_ℓ})^t`;
2. `u^N ψ(u) ≤ ψ(1)^{1−t}(X^N ψ(X))^t`;
3. if `ψ(1) ≤ B` and `X^N ψ(X) ≤ B`, then `u^N ψ(u) ≤ B`.

**Formalization Note.** The step is stated for every such finite family; by Lemma 4.5, `Ψ_X` is
one. Real powers are `Real.rpow`. -/
theorem holder_step (L N : ℕ) (c r : Fin L → ℝ) (X u : ℝ) (hc : ∀ l, 0 < c l)
    (hr : ∀ l, 0 ≤ r l) (hX : 1 < X) (hu1 : 1 < u) (huX : u < X) :
    let t := Real.log u / Real.log X
    let ψ : ℝ → ℝ := fun s => ∑ l, c l * s ^ (-r l)
    (u ^ N * ψ u = ∑ l, c l ^ (1 - t) * (c l * X ^ ((N : ℝ) - r l)) ^ t) ∧
      u ^ N * ψ u ≤ ψ 1 ^ (1 - t) * (X ^ N * ψ X) ^ t ∧
      ∀ B : ℝ, ψ 1 ≤ B → X ^ N * ψ X ≤ B → u ^ N * ψ u ≤ B := by sorry

end IntQuotHNP
