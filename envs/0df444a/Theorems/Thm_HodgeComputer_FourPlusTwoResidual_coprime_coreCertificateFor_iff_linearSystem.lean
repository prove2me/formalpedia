-- Prove2me | Theorems.Thm_HodgeComputer_FourPlusTwoResidual_coprime_coreCertificateFor_iff_linearSystem
-- name    : HodgeComputer.FourPlusTwoResidual.coprime_coreCertificateFor_iff_linearSystem
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-21T13:53:32.396452+00:00
-- url     : https://prove2.me/theorems/f84d7ecd-5bdb-4e78-a993-699b645db74c
-- title:
--   Degree-lowering linear (N, T) system equivalence for core certificates with H not dividing D
-- statement:
--   Let $S$ be any homogeneous sextic in $\mathbb{C}[x_0, x_1, y_0, y_1]$, let $D \neq 0$ be homogeneous of degree $d \ge 0$ with $H \nmid D$ (no squarefreeness assumption on $D$), and let $N_0, \dots, N_3$ be homogeneous of degree $d + 1$. Then `CoreCertificateFor S D N` ($F_H(S, D, N) = 0$, output degree $2d + 6$) holds if and only if there exists a homogeneous polynomial $T$ of degree $d$ satisfying the lower-degree linear pair
--
--   $$
--   \sum_{i=0}^3 (\partial_i D) N_i = D T \quad (\deg 2d) \qquad \text{and} \qquad 2 S D - 2 \sum_{i=0}^3 (\partial_i H) N_i + 3 H \Bigl(\sum_{i=0}^3 \partial_i N_i - T\Bigr) = 0 \quad (\deg d + 6).
--   $$
--
--   **Formalization Note** Uses `Irreducible core` to deduce `IsRelPrime D core` directly from `¬ (core ∣ D)` without requiring $D$ to be squarefree.
-- source:
--   Hodge.computer Atlas instance `four-plus-two-residual` and GitHub Discussion #120, https://github.com/hodge-computer/sextics/discussions/120

import Definitions.Def_HodgeComputerFourPlusTwoSourceAlgebra

theorem HodgeComputer.FourPlusTwoResidual.coprime_coreCertificateFor_iff_linearSystem
    (d : ℕ) (S D : MvPolynomial (Fin 4) ℂ) (N : Fin 4 → MvPolynomial (Fin 4) ℂ)
    (hS : S.IsHomogeneous 6) (hD_ne : D ≠ 0) (hDd : D.IsHomogeneous d)
    (hNd : ∀ i, (N i).IsHomogeneous (d + 1))
    (hndvd : ¬ (HodgeComputer.FourPlusTwoResidual.core ∣ D)) :
    HodgeComputer.FourPlusTwoResidual.CoreCertificateFor S D N ↔
      ∃ T : MvPolynomial (Fin 4) ℂ,
        T.IsHomogeneous d ∧
          HodgeComputer.FourPlusTwoResidual.CoprimeLinearCoreSystem S D N T := by sorry
