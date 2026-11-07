-- Prove2me | Theorems.Thm_MultiphaseDisj_claim_3_2
-- name    : MultiphaseDisj.claim_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:29:30.852184+00:00
-- url     : https://prove2.me/theorems/c67ca8d1-22cd-4f38-9ff5-8ae4976c963f
-- title:
--   Claim 3.2 — parameters of the hard distribution
-- statement:
--   Let $0<c_1\le c_2$. Write $t=t_uw$, $\beta=t^4$, let $\ell$ be the number of epochs, $n_i=\ell\beta^i$, $s_i=t^{2i}$ and $I$ the Chronogram epochs. There are absolute constants $a,b>0$ and, for every $c_1,c_2$, an $n_0$ such that for every $n\ge n_0$, every $w$ with $c_1\ln n\le w\le c_2\ln n$ and every integer $t_u\ge1$ with $t_uw\le n^{1/95}$:
--
--   1. (a) $\displaystyle a\,\frac{\log n}{\log(t_uw)}\le\ell\le b\,\frac{\log n}{\log(t_uw)}$, $\ell\ge20$, and $|I|\ge(\ell-4)/3$;
--   2. (b) $s_i\ge n^{1/3}$ for every $i\in I$;
--   3. (c) for $2\le i\le\ell$: $s_i/s_{i-1}=\sqrt\beta=(t_uw)^2$ and $\sum_{j<i}s_j\le 2s_{i-1}$; and $s_\ell\le\sqrt n$;
--   4. (d) for every $i\in[\ell]$,
--   $$
--   \mathbb E_{\mathcal D,Q}\big[|S_Q^{(i)}\cap X^{(i)}|\big]=\frac{s_i^2}{n_i}=\frac1\ell,\qquad\text{and}\qquad \Pr_{\mathcal D,Q}[S_Q\cap X=\emptyset]\ge\Big(1-\frac1\ell\Big)^{\ell}\ge\frac14 .
--   $$
--
--   These are the parameter facts on which the whole lower bound rests: (a) and (b) give $\Omega(\ell)$ epochs whose set sizes are polynomial in $n$, (c) says that the epochs after epoch $i$ insert few elements, and (d) that the answer is "disjoint" with constant probability while every block can change it.
--
--   Differences from the source:
--   - reading: standing assumptions of §3 (w = Θ(log n), tu w ≤ n^{1/95}, tq ≤ log² n, tu, tq ≥ 1, n sufficiently large) → hypotheses: ∀ 0 < c₁ ≤ c₂, ∃ n₀, ∀ n ≥ n₀, ∀ w with c₁ ln n ≤ w ≤ c₂ ln n, 1 ≤ tu, tu w ≤ n^{1/95} (tq does not occur in this claim, so its standing bounds are not hypotheses); reason: §3.1 Setup, p.16, and §2.1 'state asymptotic bounds for sufficiently large instances'
--   - reading: ℓ = Θ(log n/ log(tuw)) → absolute constants a, b > 0, chosen before c₁, c₂, with a·log n/log(tu w) ≤ ℓ ≤ b·log n/log(tu w); reason: the proof (p.16) gives absolute constants; this is the stronger reading of Θ
--   - encoding: (c) for the epochs i with s_{i−1} defined → (c) for 2 ≤ i ≤ ℓ; reason: s_{i−1} is an epoch's set size exactly when i ≥ 2
--   - reading: '(1 − 1/ℓ)^ℓ ≥ 1/4 for ℓ ≥ 2' → stated under the standing hypotheses, which give ℓ ≥ 20 by (a); reason: the condition ℓ ≥ 2 holds there
--   - encoding: pairwise disjoint blocks B₁, …, B_ℓ ⊆ [n] with |Bᵢ| = nᵢ (any choice) → the consecutive intervals of lengths n₁, …, n_ℓ; reason: the paper chooses one such family; this is a choice
--   - encoding: E_{D,Q}, Pr_{D,Q}; logarithms in (a) → finite sums under the product of the hard law and the uniform law of Q; natural logarithms in (a); reason: the ratio in (a) does not depend on the base
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Claim 3.2, p.15 (proof p.16)

import Mathlib
import Definitions.Def_MultiphaseDisj_HardDist

set_option autoImplicit false

namespace MultiphaseDisj

/-- **Claim 3.2 (Parameters)** (Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held
version sha256 ba26649b…, Claim 3.2, p.15; proof p.16). With `t = tu w`, `β = t⁴`, the
number of epochs `ℓ`, block sizes `nᵢ = ℓβⁱ`, set sizes `sᵢ = β^{i/2}` and the Chronogram epochs
`I`, the hard distribution has the following properties.

* (a) `ℓ = Θ(log n / log(tu w))`, `ℓ ≥ 20`, and `|I| ≥ (ℓ − 4)/3`.
* (b) For `i ∈ I`: `sᵢ ≥ n^{1/3}`.
* (c) `sᵢ/s_{i−1} = √β = (tu w)²`, `Σ_{j<i} s_j ≤ 2 s_{i−1}`, and `s_ℓ ≤ √n`.
* (d) `E_{D,Q}[|S_Q^{(i)} ∩ X^{(i)}|] = sᵢ²/nᵢ = 1/ℓ` for every `i`, and
  `Pr_{D,Q}[S_Q ∩ X = ∅] ≥ (1 − 1/ℓ)^ℓ ≥ 1/4`.

**Formalization Note** The standing assumptions of §3 (p.16, Setup; §2.1 "sufficiently large
instances") are hypotheses: `w = Θ(log n)` as `c₁ log n ≤ w ≤ c₂ log n` for arbitrary
`0 < c₁ ≤ c₂`, `n ≥ n₀(c₁, c₂)`, `tu ≥ 1` and `tu w ≤ n^{1/95}`. The `Θ` of (a) has absolute
constants `a, b`, chosen before `c₁, c₂`. (c) is stated for `2 ≤ i ≤ ℓ`, where `s_{i−1}` is an
epoch's set size. Epochs are `1`-based; logarithms in (a) are natural (the ratio does not depend
on the base). -/
theorem claim_3_2 :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ c₂ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ w : ℕ, c₁ * Real.log n ≤ w → (w : ℝ) ≤ c₂ * Real.log n →
      ∀ tu : ℕ, 1 ≤ tu → ((tu * w : ℕ) : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 95) →
      -- (a)
      (a * (Real.log n / Real.log ((tu * w : ℕ) : ℝ)) ≤ (ell n (tu * w) : ℝ) ∧
        (ell n (tu * w) : ℝ) ≤ b * (Real.log n / Real.log ((tu * w : ℕ) : ℝ)) ∧
        20 ≤ ell n (tu * w) ∧
        ((ell n (tu * w) : ℝ) - 4) / 3 ≤ ((epochSet n (tu * w)).card : ℝ)) ∧
      -- (b)
      (∀ i ∈ epochSet n (tu * w), (n : ℝ) ^ ((1 : ℝ) / 3) ≤ (setSize (tu * w) i : ℝ)) ∧
      -- (c)
      (∀ i : ℕ, 2 ≤ i → i ≤ ell n (tu * w) →
        (setSize (tu * w) i : ℝ) / (setSize (tu * w) (i - 1) : ℝ) =
            Real.sqrt (beta (tu * w) : ℝ) ∧
          Real.sqrt (beta (tu * w) : ℝ) = ((tu * w : ℕ) : ℝ) ^ 2 ∧
          ∑ j ∈ Finset.Ico 1 i, setSize (tu * w) j ≤ 2 * setSize (tu * w) (i - 1)) ∧
      (setSize (tu * w) (ell n (tu * w)) : ℝ) ≤ Real.sqrt n ∧
      -- (d)
      (∀ i ∈ Finset.Icc 1 (ell n (tu * w)),
        expect (dqLaw n (tu * w)) (fun ω =>
            (((ω.1.1 ω.2 ∩ block n (tu * w) i) ∩ (ω.1.2 ∩ block n (tu * w) i)).card : ℝ)) =
          (setSize (tu * w) i : ℝ) ^ 2 / (blockSize n (tu * w) i : ℝ) ∧
        (setSize (tu * w) i : ℝ) ^ 2 / (blockSize n (tu * w) i : ℝ) =
          1 / (ell n (tu * w) : ℝ)) ∧
      (1 - 1 / (ell n (tu * w) : ℝ)) ^ ell n (tu * w) ≤
        pr (dqLaw n (tu * w)) (fun ω => Disjoint (ω.1.1 ω.2) ω.1.2) ∧
      (1 : ℝ) / 4 ≤ (1 - 1 / (ell n (tu * w) : ℝ)) ^ ell n (tu * w) := by sorry

end MultiphaseDisj
