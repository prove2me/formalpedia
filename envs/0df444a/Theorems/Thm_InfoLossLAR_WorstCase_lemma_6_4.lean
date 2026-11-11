-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_lemma_6_4
-- name    : InfoLossLAR.WorstCase.lemma_6_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:03:54.441252+00:00
-- url     : https://prove2.me/theorems/a6a9695c-a143-4fe6-aad6-0a7debe60ac5
-- title:
--   Lemma 6.4 — $\mathcal L(T)=\{z:\sum_j z_j\equiv0\ (\mathrm{mod}\ q)\}$, index $q$, Smith form $\operatorname{diag}(I_{d-1},q)$
-- statement:
--   Let $q$ be an odd prime, $d\ge q$, and $T$ the matrix of Definition 6.3. Then
--   $$\mathcal L(T)=\Big\{z\in\mathbb Z^d:\sum_{j=1}^d z_j\equiv0\pmod q\Big\},$$
--   this lattice has index $q$ in $\mathbb Z^d$, and the Smith normal form of $T$ is $\operatorname{diag}(I_{d-1},q)$: there are unimodular $U,V$ with $UTV=\operatorname{diag}(I_{d-1},q)$. Consequently $T$ is a rounding matrix with $r=d-1$ and $\ell=1$ (Definition 2.3).
--
--   Differences from the source:
--   - encoding: "index $q$ in $\mathbb Z^d$" → `AddSubgroup.index` of $\mathcal L(T)$ equals $q$; reason: same notion
--   - encoding: "the Smith normal form of $T$ is $\operatorname{diag}(I_{d-1},q)$; $T$ is a rounding matrix with $r=d-1$, $\ell=1$" → `IsRoundingMatrix q (d-1) d T` (unimodular $U,V$ with $UTV=\operatorname{diag}(I_{d-1},q)$); reason: the two clauses say the same thing
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 27, Lemma 6.4

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_Rounding
import Definitions.Def_InfoLossLAR_WorstCase_FixedT

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

/-- Lemma 6.4 (Image lattice and Smith normal form), p. 27: for `q` an odd prime, `d ≥ q` and
`T` of Definition 6.3, `L(T) = {z ∈ ℤ^d : ∑_j z_j ≡ 0 (mod q)}`, this lattice has index `q` in
`ℤ^d`, and the Smith normal form of `T` is `diag(I_{d−1}, q)` (there are unimodular `U, V` with
`UTV = diag(I_{d−1}, q)`), so `T` is a rounding matrix with `r = d − 1`, `ℓ = 1`. -/
theorem lemma_6_4 (q d : ℕ) (hq : q.Prime) (hq2 : q ≠ 2) (hdq : q ≤ d) :
    (∀ z : Fin d → ℤ, z ∈ imageLattice (TDef63 q d) ↔ (q : ℤ) ∣ ∑ j, z j) ∧
    (imageLattice (TDef63 q d)).toAddSubgroup.index = q ∧
    IsRoundingMatrix q (d - 1) d (TDef63 q d) := by sorry

end InfoLossLAR.WorstCase
