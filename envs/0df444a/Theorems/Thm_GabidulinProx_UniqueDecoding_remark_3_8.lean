-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_remark_3_8
-- name    : GabidulinProx.UniqueDecoding.remark_3_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:03.404236+00:00
-- url     : https://prove2.me/theorems/3be5372b-622e-45e3-87e7-a3eef794c3d7
-- title:
--   Remark 3.8 — the explicit bound τₑ ≤ 10qⁿ⁻¹
-- statement:
--   Let $q,n,k,e$ be natural numbers satisfying $q\ge2$, $1\le k\le n$, $e\ge1$, and $2e<n-k+1$. For $\sigma_r=\sum_{i=0}^rq^i$ and $\tau_e=(\sigma_e-1)+\sigma_e((\sigma_e-1)\sigma_{k-1}+1)$,
--
--   with $r=q/(q-1)$ all the steps of the remark hold:
--
--   $$\tau_e\le r^3q^{k+2e-1}+2rq^e,\qquad \tau_e\le r^3q^{n-1}+2rq^{n-2}=\Bigl[r^3+\frac{2}{q-1}\Bigr]q^{n-1}\le10q^{n-1}.$$
--
--   Consequently, for every natural number $s$, if $s>10q^{n-1}$ then $s>\tau_e$; with $s=|S|$ this says that the count condition $|S|>10q^{n-1}$ implies the hypothesis $|S|>\tau_e$ of Theorem 3.3. The parameter range forces $n\ge3$, so $n-1$, $n-2$ and $k+2e-1$ do not truncate.
--
--   Differences from the source:
--   - generalization: $q$ is a prime power coming from a finite field → any natural number $q\ge2$; reason: the stated numerical bound depends only on this inequality; every prime-power instance is included
--   - encoding: $e<d/2$ for $d=n-k+1$ → $2e<n-k+1$ in natural-number arithmetic; reason: the multiplied inequality is equivalent, with $1\le k\le n$ preventing underflow
--   - encoding: the count $|S|$ of good parameters in "the hypothesis of Theorem 3.3 is implied by $|S|>10q^{n-1}$" → an arbitrary natural number $s$ in $10q^{n-1}<s\Rightarrow\tau_e<s$; reason: the implication is numerical; $s=|S|$ gives the source sentence, and $|S|>\tau_e$ is the hypothesis $\Pr>\tau_e/q^m$ of Theorem 3.3 multiplied by $q^m$
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Remark 3.8 p.24. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf

import Definitions.Def_GabidulinProx_UniqueDecoding_Codes

namespace GabidulinProx.UniqueDecoding

/-- Remark 3.8, p.24: its chain of bounds, the final τ_e ≤ 10q^(n-1), and the count
consequence, with `s` standing for |S|. The statement is independent of a field realization. -/
theorem remark_3_8 (q n k e : ℕ) (hq : 2 ≤ q) (hk : 1 ≤ k) (hkn : k ≤ n)
    (he : 1 ≤ e) (hdec : 2 * e < n - k + 1) :
    let r : ℝ := (q : ℝ) / ((q : ℝ) - 1)
    (tau q k e : ℝ) ≤ r ^ 3 * (q : ℝ) ^ (k + 2 * e - 1) + 2 * r * (q : ℝ) ^ e ∧
    (tau q k e : ℝ) ≤ r ^ 3 * (q : ℝ) ^ (n - 1) + 2 * r * (q : ℝ) ^ (n - 2) ∧
    r ^ 3 * (q : ℝ) ^ (n - 1) + 2 * r * (q : ℝ) ^ (n - 2) =
      (r ^ 3 + 2 / ((q : ℝ) - 1)) * (q : ℝ) ^ (n - 1) ∧
    (r ^ 3 + 2 / ((q : ℝ) - 1)) * (q : ℝ) ^ (n - 1) ≤ 10 * (q : ℝ) ^ (n - 1) ∧
    tau q k e ≤ 10 * q ^ (n - 1) ∧
    ∀ s : ℕ, 10 * q ^ (n - 1) < s → tau q k e < s := by sorry

end GabidulinProx.UniqueDecoding
