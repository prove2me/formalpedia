-- Prove2me | Theorems.Thm_L22EigEst_lemma_4_10
-- name    : L22EigEst.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:21:09.53275+00:00
-- url     : https://prove2.me/theorems/e148dd92-4b18-4812-923d-54fa6a28d6c3
-- title:
--   Lemma 4.10 — decoupled bound on $\mathbb E\|SHS^\top\|_2$ for a zero-diagonal symmetric $H$
-- statement:
--   There is a universal constant $C_0>0$ such that the following holds. Let $H$ be a symmetric $n\times n$ matrix with all-zero diagonal, let $p_1,\dots,p_n\in(0,1]$, and let $S$ be the random row-sampling matrix that includes row $i$ independently with probability $p_i$ and rescales it by $1/\sqrt{p_i}$; let $S'$ be an independent copy of $S$ and $|S|$ the number of sampled rows. Then
--
--   $$\mathbb E_S\|SHS^\top\|_2\le4\|H\|_2+4C_0\Big(\mathbb E_S\big[\log(e+|S|)\,\|HS^\top\|_{1\to2}^2\big]\Big)^{1/2}+4C_0\,\mathbb E_S\Big[\Big(\mathbb E_{S'}\big[\log(e+|S'|)\,\|SHS'^\top\|_{1\to2}^2\big]\Big)^{1/2}\Big],\tag{6}$$
--
--   where $\|\cdot\|_2$ is the spectral norm and $\|\cdot\|_{1\to2}$ the maximum column norm.
--
--   This is Theorem 1.1 of [Tro08] in the form of [MW27], with the constant $C_0$ of the Rudelson–Vershynin bound (Theorem 10); it carries only $\sqrt{\log|S|}$, not $\sqrt{\log n}$. It is the first step of the proof of Lemma 4.4.
--
--   Differences from the source:
--   - reading: "for the universal constant C0 of Theorem 10" → there exists a universal constant C₀ > 0 (chosen before n, H, p); reason: Theorem 10 is not posed in this mission; it asserts only the existence of a universal C₀
--   - encoding: S includes row i with probability p_i and rescales it by 1/√p_i → p_i ∈ (0, 1]; reason: the rescaling 1/√p_i is undefined at p_i = 0
--   - encoding: S ∈ ℝ^{s×n} (or its n × n view) and E_S, Pr_S over the draw of S → the n × n diagonal view S_ii = δ_i/√p_i (sampMat), probabilities and expectations as finite sums over the 2ⁿ patterns δ (bernProb, bernExp); reason: the paper uses the two views interchangeably (p.9); a finite product of Bernoulli laws is exactly this sum
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Lemma 4.10, p.17, eq. (6)

import Definitions.Def_L22EigEst_bernW
import Definitions.Def_L22EigEst_sampMat
import Definitions.Def_L22EigEst_colNorm12
import Definitions.Def_WainwrightHDS_EigPert_opNorm2

open WainwrightHDS.EigPert

namespace L22EigEst

/-- **Lemma 4.10** (Theorem 1.1 in [Tro08], p.17), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…): "Let H be a symmetric n × n matrix with an all-zero
diagonal, and let S be a row-sampling matrix that includes the i-th row with probability p_i and
rescales it by 1/√p_i. Then, for the universal constant C0 of Theorem 10,
E_S[∥SHS⊺∥2] ≤ 4∥H∥2 + 4C0 (E_S[log(e + |S|) · ∥HS⊺∥²_{1→2}])^{1/2}
+ 4C0 E_S[(E_S′[log(e + |S′|) · ∥SHS′⊺∥²_{1→2}])^{1/2}]. (6) where S′ is an independent copy of S."

**Formalization Note.** `S = sampMat p δ` (`n × n` view, `S⊺ = S`), `δ_i ∼ Ber(p_i)` independent,
expectations as finite sums (`bernExp`); `S′` is a second pattern `δ′` with the same law,
independent of `δ`. `|S|` is `sampCount δ`, `‖·‖₂` is `opNorm2`, `‖·‖_{1→2}` is `colNorm12`, `log`
natural. Theorem 10 is not posed: `C₀` is a universal constant, existential here and chosen before
`n`, `H` and `p`. `0 < p_i` makes the rescaling `1/√p_i` defined. -/
theorem lemma_4_10 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ),
      H.IsHermitian → (∀ i, H i i = 0) → (∀ i, 0 < p i ∧ p i ≤ 1) →
      bernExp p (fun δ => opNorm2 (sampMat p δ * H * sampMat p δ)) ≤
        4 * opNorm2 H +
        4 * C₀ * Real.sqrt (bernExp p (fun δ =>
          Real.log (Real.exp 1 + sampCount δ) * colNorm12 (H * sampMat p δ) ^ 2)) +
        4 * C₀ * bernExp p (fun δ => Real.sqrt (bernExp p (fun δ' =>
          Real.log (Real.exp 1 + sampCount δ') *
            colNorm12 (sampMat p δ * H * sampMat p δ') ^ 2))) := by sorry

end L22EigEst
