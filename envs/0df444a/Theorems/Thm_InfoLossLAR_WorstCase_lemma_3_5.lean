-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_lemma_3_5
-- name    : InfoLossLAR.WorstCase.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:03:24.563203+00:00
-- url     : https://prove2.me/theorems/80d07148-040c-44bc-ba6b-022553ce05ac
-- title:
--   Lemma 3.5 — basic properties of LAR: quotient encoding, translation equivariance, balanced fibers
-- statement:
--   Let $q$ be an odd prime, $d\ge1$, and $T\in\mathbb Z^{d\times d}$ a rounding matrix of modular rank $r$ with chosen Smith matrices, $\ell=d-r$ (the case $\ell=0$ included), $P$, $J$, $\mathrm{AR}_T$ and $f_T$ as in Definitions 3.1–3.4. Then:
--
--   *Well-defined quotient encoding.* For all $x,z\in\mathbb Z^d$, $\mathrm{AR}_T(x+qz)=\mathrm{AR}_T(x)+Tz$; the map $z\mapsto Pz\bmod q$ is onto $\mathbb F_q^\ell$ with kernel $\mathcal L(T)$, so it induces $\mathbb Z^d/\mathcal L(T)\cong\mathbb F_q^\ell$; and for every $x\in\mathbb F_q^d$ and every integer lift $y$ of $x$, $P\,\mathrm{AR}_T(y)\bmod q=f_T(x)$.
--
--   *Translation equivariance.* The columns of $J$ are linearly independent over $\mathbb F_q$ and span $\ker(T\bmod q)$, and
--   $$f_T(x+Ja)=f_T(x)+a\qquad(x\in\mathbb F_q^d,\ a\in\mathbb F_q^\ell).$$
--
--   *Balanced fibers.* For every $y\in\mathbb F_q^\ell$, $|\{x\in\mathbb F_q^d:f_T(x)=y\}|=q^r$.
--
--   Differences from the source:
--   - encoding: "$f_T(x)$ encodes the quotient output $\mathrm{AR}_T([x]_q)+\mathcal L(T)$" → the isomorphism clause (surjective, kernel $\mathcal L(T)$) applied to $\mathrm{AR}_T([x]_q)$; reason: this is what "encodes" means
--   - encoding: "$J$ has full column rank over $\mathbb F_q$" → the columns of $J$ are linearly independent; reason: same notion
--   - encoding: odd prime $q$, fixed Smith matrices, indices $1..d$ → `[Fact q.Prime]`, `q ≠ 2`, `SmithData q r d T`, `Fin d`; reason: Lean conventions
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 19, Lemma 3.5

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_Rounding

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

/-- Lemma 3.5 (Basic properties of LAR), p. 19, for a rounding matrix `T` of modular rank `r`
with chosen Smith matrices (`q` an odd prime, `d ≥ 1`, `ℓ = d − r`, `ℓ = 0` allowed):
well-defined quotient encoding (`AR_T(x + qz) = AR_T(x) + Tz`; `z ↦ Pz mod q` is onto `𝔽_q^ℓ`
with kernel `L(T)`; `f_T(x)` is the same for every integer lift of `x`), translation
equivariance (the columns of `J` are linearly independent over `𝔽_q` and span
`ker(T mod q)`; `f_T(x + Ja) = f_T(x) + a`), and balanced fibers (`|f_T^{-1}(y)| = q^r`). -/
theorem lemma_3_5 (q r d : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hd : 1 ≤ d)
    (T : Matrix (Fin d) (Fin d) ℤ) (S : SmithData q r d T) :
    (∀ x z : Fin d → ℤ, AR q T (x + (q : ℤ) • z) = AR q T x + T.mulVec z) ∧
    Function.Surjective (fun z : Fin d → ℤ => modq q (S.P.mulVec z)) ∧
    (∀ z : Fin d → ℤ, modq q (S.P.mulVec z) = 0 ↔ z ∈ imageLattice T) ∧
    (∀ (x : Fin d → ZMod q) (y : Fin d → ℤ), modq q y = x →
      modq q (S.P.mulVec (AR q T y)) = S.fT x) ∧
    LinearIndependent (ZMod q) (fun j : Fin (d - r) => fun i : Fin d => S.J i j) ∧
    Submodule.span (ZMod q) (Set.range fun j : Fin (d - r) => fun i : Fin d => S.J i j) =
      LinearMap.ker (Matrix.mulVecLin (matModq q T)) ∧
    (∀ (x : Fin d → ZMod q) (a : Fin (d - r) → ZMod q), S.fT (x + S.J.mulVec a) = S.fT x + a) ∧
    (∀ y : Fin (d - r) → ZMod q,
      (Finset.univ.filter fun x : Fin d → ZMod q => S.fT x = y).card = q ^ r) := by sorry

end InfoLossLAR.WorstCase
