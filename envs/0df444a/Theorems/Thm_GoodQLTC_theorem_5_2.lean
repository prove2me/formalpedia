-- Prove2me | Theorems.Thm_GoodQLTC_theorem_5_2
-- name    : GoodQLTC.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:57:51.307454+00:00
-- url     : https://prove2.me/theorems/49e9c133-d9c5-4601-b026-b34a17ff0937
-- title:
--   Theorem 5.2: dimension and rate
-- statement:
--   Let $X$ be a regular $t$-dimensional cubical complex (degrees $2\le n_1\le\dots\le n_t$) and $\mathcal F$ an $\mathbb F_{2^s}$-cosheaf with compatible base codes of dimensions $0<m_{i,b}<n_i$; put $A=|X(t)|$. For $2\le k\le t-2$ and $J\subseteq[t]$ with $|J|=k$,
--   $$
--   h_k\ge A\,\Gamma_k(J)\qquad\text{and}\qquad \frac{K(Q)}{N}\ge\frac{\Gamma_k(J)}{\mathrm{sym}_{t-k}(S_1,\dots,S_t)},
--   $$
--   where $Q$ is the code of Equation (4.5) (for any ordered $\mathbb F_2$-basis $\beta$).
--
--   This is the rate bound of the construction.
--
--   Differences from the source:
--   - encoding: choose bases of all stalks → stalks are coordinate spaces F^{d(f)} (a cosheaf with chosen bases); reason: a cosheaf with a choice of stalk bases is exactly this data; (4.5) depends only on the matrices in those bases
--   - encoding: an ordered F_2-basis β of F → an additive isomorphism F ≃ F_2^s; reason: the coordinate map of an ordered basis; every additive isomorphism of F_2-spaces is F_2-linear
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Theorem 5.2, p.20 (PDF p.23)

import Mathlib
import Definitions.Def_GoodQLTC_logicalQubits
import Definitions.Def_GoodQLTC_IsCubicalComplex
import Definitions.Def_GoodQLTC_IsRegular
import Definitions.Def_GoodQLTC_BaseCodeData
import Definitions.Def_GoodQLTC_cobdMat
import Definitions.Def_GoodQLTC_cssHX
import Definitions.Def_GoodQLTC_rateGamma

namespace GoodQLTC

/-- **Theorem 5.2** (rate), Gay–Jeronimo, arXiv:2609.20780 (held version), p.20: let `X` be a
regular `t`-dimensional cubical complex and `F` an `F`-cosheaf with compatible base codes. For
`2 ≤ k ≤ t − 2` and `J ⊆ [t]` with `|J| = k`,
`h_k ≥ A Γ_k(J)` and `K(Q)/N ≥ Γ_k(J)/sym_{t−k}(S_1, …, S_t)`,
where `Q` is the code of Equation (4.5) and `A := V D_{[t]} = |X(t)|`.

**Formalization Note.** Standing assumptions of §4: degrees `2 ≤ n_1 ≤ ⋯ ≤ n_t`, endpoint
dimensions `0 < m_{i,b} < n_i`, `|F| = 2^s` with `s ≥ 1`; `β` is any ordered `F_2`-basis of `F`.
`A` is `numFaces φ t`, `N` the number of columns of `H_X`. -/
theorem theorem_5_2 {t : ℕ} {X : Type} [PartialOrder X] [Fintype X]
    {φ : X → Fin t → Option Bool} {n : Fin t → ℕ} (hn : ∀ i, 2 ≤ n i) (hmono : Monotone n)
    (hX : IsCubicalComplex t φ) (hreg : IsRegular φ n)
    {F : Type} [Field F] [Fintype F] {s : ℕ} (hs : 1 ≤ s) (hF : Fintype.card F = 2 ^ s)
    (Fs : Cosheaf X F) {m : Fin t → Bool → ℕ} (hm : ∀ i b, 0 < m i b ∧ m i b < n i)
    (D : BaseCodeData φ Fs m) (hD : IsCompatible D) (β : F ≃+ (Fin s → ZMod 2))
    (k : ℕ) (hk : 2 ≤ k) (hkt : k + 2 ≤ t) (J : Finset (Fin t)) (hJ : J.card = k) :
    (numFaces φ t : ℝ) * rateGamma n m k J ≤ (cohomDim φ Fs k : ℝ) ∧
    rateGamma n m k J / esym (rateS n m) (t - k) ≤
      (logicalQubits (cssHX φ Fs β k) (cssHZ φ Fs β k) : ℝ) /
        (Fintype.card ((Σ f : Face φ k, Fin (Fs.d f.1)) × Fin s) : ℝ) := by sorry

end GoodQLTC
