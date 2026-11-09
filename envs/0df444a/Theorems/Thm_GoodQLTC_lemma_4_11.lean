-- Prove2me | Theorems.Thm_GoodQLTC_lemma_4_11
-- name    : GoodQLTC.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:55:59.147652+00:00
-- url     : https://prove2.me/theorems/60d09c7f-6349-4efb-96e7-3ff0eb8f89c8
-- title:
--   Lemma 4.11: the CSS code of a cosheaf
-- statement:
--   Let $X$ be a regular $t$-dimensional cubical complex with degrees $2\le n_1\le\dots\le n_t$, $F$ a field with $2^s$ elements ($s\ge1$), $\mathcal F$ an $F$-cosheaf on $X$, $\beta$ an ordered $\mathbb F_2$-basis of $F$, and $1\le k<t$. The matrices of Equation (4.5), $H_X=R_\beta(\delta^k)$ and $H_Z=R_\beta(\delta^{k-1})^{\top}$, define a binary CSS code $Q$ on
--   $$
--   N=sM_k\ \text{physical qubits, encoding}\ K(Q)=s\,h_k\ \text{logical qubits, with}\ m_X=sM_{k+1},\ m_Z=sM_{k-1}.
--   $$
--
--   This identifies the code parameters with the cohomology of the cosheaf.
--
--   **Formalization Note** The number of qubits and checks are the cardinalities of the column and row index types of `cssHX`/`cssHZ`.
--
--   Differences from the source:
--   - encoding: choose bases of all stalks → stalks are coordinate spaces F^{d(f)} (a cosheaf with chosen bases); reason: a cosheaf with a choice of stalk bases is exactly this data; (4.5) depends only on the matrices in those bases
--   - encoding: an ordered F_2-basis β of F → an additive isomorphism F ≃ F_2^s; reason: the coordinate map of an ordered basis; every additive isomorphism of F_2-spaces is F_2-linear
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), Lemma 4.11, p.18 (PDF p.21)

import Mathlib
import Definitions.Def_GoodQLTC_IsCSS
import Definitions.Def_GoodQLTC_logicalQubits
import Definitions.Def_GoodQLTC_IsCubicalComplex
import Definitions.Def_GoodQLTC_IsRegular
import Definitions.Def_GoodQLTC_cobdMat
import Definitions.Def_GoodQLTC_cssHX

namespace GoodQLTC

/-- **Lemma 4.11** (the CSS code of a cosheaf), Gay–Jeronimo, *Asymptotically Good Quantum Locally
Testable Codes*, arXiv:2609.20780 (held version), p.18: the matrices of Equation (4.5),
`H_X := R_β(δ^k)` and `H_Z := R_β(δ^{k−1})^⊺` (`1 ≤ k < t`), define a binary CSS code `Q` on
`N = s M_k` physical qubits encoding `K(Q) = s h_k` logical qubits with `m_X = s M_{k+1}` and
`m_Z = s M_{k−1}`.

**Formalization Note.** `X` is a regular `t`-dimensional cubical complex with degrees
`2 ≤ n_1 ≤ ⋯ ≤ n_t` (the standing assumption of §4); `F` is a field with `2^s` elements, `s ≥ 1`;
stalks are coordinate spaces (stalk bases chosen); `β` is any ordered `F_2`-basis of `F`. The
qubits, X-checks and Z-checks are the column and row index types of `cssHX`/`cssHZ`. -/
theorem lemma_4_11 {t : ℕ} {X : Type} [PartialOrder X] [Fintype X]
    {φ : X → Fin t → Option Bool} {n : Fin t → ℕ} (hn : ∀ i, 2 ≤ n i) (hmono : Monotone n)
    (hX : IsCubicalComplex t φ) (hreg : IsRegular φ n)
    {F : Type} [Field F] [Fintype F] {s : ℕ} (hs : 1 ≤ s) (hF : Fintype.card F = 2 ^ s)
    (Fs : Cosheaf X F) (β : F ≃+ (Fin s → ZMod 2)) (k : ℕ) (hk : 1 ≤ k) (hkt : k < t) :
    IsCSS (cssHX φ Fs β k) (cssHZ φ Fs β k) ∧
    Fintype.card ((Σ f : Face φ k, Fin (Fs.d f.1)) × Fin s) = s * cochainDim φ Fs k ∧
    logicalQubits (cssHX φ Fs β k) (cssHZ φ Fs β k) = (s : ℤ) * (cohomDim φ Fs k : ℤ) ∧
    Fintype.card ((Σ g : Face φ (k + 1), Fin (Fs.d g.1)) × Fin s) =
      s * cochainDim φ Fs (k + 1) ∧
    Fintype.card ((Σ g : Face φ (k - 1), Fin (Fs.d g.1)) × Fin s) =
      s * cochainDim φ Fs (k - 1) := by sorry

end GoodQLTC
